#!/usr/bin/env python3

# depends on i3ipc==2.2.1 and Box2D==2.3.2
# also depends on the pw-dump command and jq (1.7.1)

import os
import threading
from time import sleep, monotonic
from random import random

import subprocess

import atexit
import math as m
import json

from enum import Enum

import i3ipc

from Box2D import b2

__license__ = "MIT"
__version__ = "v1.0.0"

# some constants
# cursed shell string (takes ~0.2s to execute on my laptop)
# output a json dict: {<pid>: [<node id>*]}
SH_GET_PIPEWIRE_PID_MAPPING = """
pw-dump | jq -c '
	([.[]|select(.type=="PipeWire:Interface:Client") |
		{key:.id|tostring,value:.info.props["pipewire.sec.pid"]}]|from_entries) as $clients
	| reduce (.[]|select(.type=="PipeWire:Interface:Node")) as $i ({};
		.[$i.info.props["application.process.id"] // $clients[$i.info.props["client.id"]|tostring]|tostring]+=[$i.id])'
"""
SQRT_1_2 = m.sqrt(2) / 2


# enable printing various state (e.g. body coordinates)
STATUS = True

# enable panning and volume control for windows via pipewire
# only works when the process that opened the window is also the process that is playing audio
# (that is, it won't work with mpv running in a terminal emulator, or with modern web browsers)
# it also only works with _stereo_ sink inputs -- that is, the media player has to output two channels
PIPEWIRE = True

# how often shall the code run the cursed shell string above to get pipewire node IDs?
PIPEWIRE_FETCH_INTERVAL = 1
# how often shall the code update the pipewire volumes?
PIPEWIRE_UPDATE_INTERVAL = 0.1

# gravitational constant (set to 0 to disable newtonian gravity)
GRAV = 0

# arena-wide acceleration value
FLAT_GRAVITY = (0, -2)

# how bouncy things are
RESTITUTION=.75

# value for the limiter, if your pc is fast enough this will be the box2d timestep
FPS=30
# we only handle one output for now
OUTPUT_NAME="eDP-1"

# shall the script only handle one workspace? (set to None to handle all workspaces)
WORKSPACE="9"
# shall the script only update the workspace when it's focused?
# (in contrast of it being merely visible, e.g. in multi-monitor setups)
ONLY_WHEN_FOCUSED=True

# box2d coordinate scale
BOX2D_SCALE=1/128

# how much mouse dragging is amplified
DRAG_SCALE=8

# in box2d coordinates
ARENA_HEIGHT=40

# if a window reaches this height it shall be closed (make sure it's higher than the initial coords)
ARENA_DISCARD_HEIGHT=25

class DuckOOBBehaviour(Enum):
	# close the window that moves out of bounds
	CLOSE = 1
	# move it to initial coordinates
	RESPAWN = 2

OOB_BEHAVIOUR = DuckOOBBehaviour.RESPAWN

# configure your sway to move floating windows to these coordinates for it to work
INITIAL_WINDOW_COORDS=(200, -1500)

class Cl3(b2.contactListener):
	collisions = []
	def PostSolve(self, contact, impulse):
		if max(impulse.normalImpulses) < 1: return
		e = max(impulse.normalImpulses)
		b1 = contact.fixtureA.body
		b2 = contact.fixtureB.body

		u1 = b1.userData.get("id") if b1 != a_walls else "wall"
		u2 = b2.userData.get("id") if b2 != a_walls else "wall"

		self.collisions.append((u1, u2, e))

cl3 = Cl3()
arena = b2.world(gravity=FLAT_GRAVITY, contactListener=cl3)

a_walls = None
arena_size = None
arena_offset = None

# floating_con id -> { body: b2Body, width: int, height: int, x: int, y: int }
windows = {}

tree = None
workspaces = None
curr_workspace = None

pw_nodes_per_pid = {}

a = i3ipc.Connection()

print()

def resize_arena(w, h, x=0, y=0):
	global arena_size, arena_offset, a_walls
	if arena_size == (w, h) and arena_offset == (x, y): return
	arena_size = (w, h)
	arena_offset = (x, y)

	if a_walls != None:
		arena.DestroyBody(a_walls)
		a_walls = None
	a_walls = arena.CreateStaticBody(
		position=(x*BOX2D_SCALE, -y*BOX2D_SCALE),
		shapes=[
			# left wall
			b2.edgeShape(vertices=[(0, 0), (0, ARENA_HEIGHT)]),
			# right wall
			b2.edgeShape(vertices=[(arena_size[0]*BOX2D_SCALE, 0), (arena_size[0]*BOX2D_SCALE, ARENA_HEIGHT)]),
			# floor
			b2.edgeShape(vertices=[(0, 0), (arena_size[0]*BOX2D_SCALE, 0)]),
			# ceiling
			b2.edgeShape(vertices=[(0, ARENA_HEIGHT), (arena_size[0]*BOX2D_SCALE, ARENA_HEIGHT)]),
		])

def create_body(container_id, initial=None):
	con = curr_workspace.find_by_id(container_id)
	assert con != None, f"no container with id {container_id}"

	width = con.rect.width
	height = con.rect.height
	x = con.rect.x
	y = con.rect.y
	body_type = b2.staticBody if con.sticky else b2.dynamicBody

	if initial == None:
		initial = (x, y) == INITIAL_WINDOW_COORDS

	data = {
		"id": container_id,
		"width": width, "height": height, "x": x, "y": y,
		"px": x, "py": y, # for tracking external window movements
		"pid": con.pid, # for pulseaudio/pipewire tomfoolery
	}

	bd = b2.bodyDef(
		type = body_type,
		awake = True,
		linearDamping = 0,
		fixedRotation = True,
		fixtures=b2.fixtureDef(
			shape=b2.polygonShape(box=(width/2*BOX2D_SCALE, height/2*BOX2D_SCALE)),
			restitution=RESTITUTION,
			density=8),
		userData = data)

	if initial:
		bd.position=(randrange(0, arena_size[0]-width)*BOX2D_SCALE, (arena_size[1]+height+100)*BOX2D_SCALE)
		bd.linearVelocity=(randrange(-8, 8), -5)
	else:
		bd.position=((x + width/2) * BOX2D_SCALE, (arena_size[1] - y - height/2) * BOX2D_SCALE)
		bd.linearVelocity=(0, 0)

	bo = arena.CreateBody(bd)

	#bo.mass = width * height * BOX2D_SCALE * BOX2D_SCALE,

	data["body"] = bo
	windows[container_id] = data

def sync_body(container_id):
	con = curr_workspace.find_by_id(container_id)
	assert con != None, f"no container with id {container_id}"

	b = windows[container_id]

	width = con.rect.width
	height = con.rect.height
	x = con.rect.x
	y = con.rect.y
	body_type = b2.staticBody if con.sticky else b2.dynamicBody

	b["body"].type = body_type

	if width == b["width"] and height == b["height"] and x == b["x"] and y == b["y"]:
		return # yeah nothing to do here
	if con.fullscreen_mode != 0:
		return # we are not dealing with fullscreen windows

	arena.DestroyBody(b["body"])

	bd = b2.bodyDef(
		type = body_type,
		awake = True,
		linearDamping = 0,
		fixedRotation = True,
		fixtures=b2.fixtureDef(
			shape=b2.polygonShape(box=(width/2*BOX2D_SCALE, height/2*BOX2D_SCALE)),
			restitution=RESTITUTION,
			density=8),
		userData = b)

	if "b2_static" in con.marks:
		bd.type = b2.staticBody

	bd.mass = width * height * BOX2D_SCALE * BOX2D_SCALE
	bd.position=((x + width/2) * BOX2D_SCALE, (arena_size[1] - y - height/2) * BOX2D_SCALE)
	if body_type != b2.staticBody:
		bd.linearVelocity=((x-b["x"])*DRAG_SCALE*BOX2D_SCALE, (b["y"]-y)*DRAG_SCALE*BOX2D_SCALE)

	sh = randrange(m.pi * 2)
	bo = arena.CreateBody(bd)

	b["px"] = b["x"]
	b["py"] = b["y"]

	b["width"] = width
	b["height"] = height
	b["x"] = x
	b["y"] = y
	b["body"] = bo

def destroy_body(container_id):
	arena.DestroyBody(windows[container_id]["body"])
	windows.pop(container_id)

def randrange(min, max=0):
	return min + random() * (max-min)

d = 1/FPS
pt = 0
t = 0

def pw_fetch_nodes_loop():
	global pw_nodes_per_pid
	while True:
		pr = subprocess.run(["sh", "-c", SH_GET_PIPEWIRE_PID_MAPPING], text=True, stdout=subprocess.PIPE)
		pw_nodes_per_pid = json.loads(pr.stdout)
		sleep(PIPEWIRE_FETCH_INTERVAL)

def pw_update_volumes_loop():
	spw = subprocess.Popen(["pw-cli"], stdin=subprocess.PIPE, stdout=subprocess.DEVNULL, text=True)
	@atexit.register
	def on_exit():
		spw.terminate()
	while True:
		for i in windows.values():
			e = i["body"].position
			mo = e - b2.vec2(arena_size[0] * BOX2D_SCALE / 2, 0)
			mv = 1 / max(1, mo.y / (arena_size[1] * BOX2D_SCALE)) ** 3
			pan = mo.x / (arena_size[0] * BOX2D_SCALE) * m.pi * .5
			al = mv*SQRT_1_2*(m.cos(pan)-m.sin(pan))
			ar = mv*SQRT_1_2*(m.cos(pan)+m.sin(pan))
			#print(f"{i['id']:> 4} {mv:> 8.03f} {pan:> 8.03f}\x1b[K")

			if (al, ar) != i.get("pw_volumes"):
				i["pw_volumes"] = [al, ar]
				so = json.dumps({"Spa:Pod:Object:Param:Props:channelVolumes": [al, ar]})
				for i in pw_nodes_per_pid.get(str(i["pid"])) or []:
					spw.stdin.write(f"s {i} 2 {so}\n")
					#print(f"s {i} 2 {so}\x1b[K\n")
		spw.stdin.flush()
		sleep(PIPEWIRE_UPDATE_INTERVAL)

if PIPEWIRE:
	threading.Thread(target=pw_fetch_nodes_loop, daemon=True).start()
	threading.Thread(target=pw_update_volumes_loop, daemon=True).start()

t = monotonic()
while True:
	sleep(max(0, (1/FPS) - t % (1/FPS)))

	pt = t
	t = monotonic()
	d = min(1, max(1/FPS, t - pt))

	#print(d)
	workspaces = a.get_workspaces()

	curr_workspace = None

	for wa in workspaces:
		#print(wa.ipc_data["id"], wa.name, wa.output, wa.rect.x, wa.rect.y, wa.rect.width, wa.rect.height)
		resize_arena(wa.rect.width, wa.rect.height, wa.rect.x, wa.rect.y)
		if wa.output == OUTPUT_NAME and wa.visible \
			and (not WORKSPACE or wa.name == WORKSPACE):
			tree = a.get_tree()
			curr_workspace = tree.find_by_id(wa.ipc_data["id"])
			if ONLY_WHEN_FOCUSED and not curr_workspace.find_focused() and not curr_workspace.focused:
				curr_workspace = None
			break

	if curr_workspace == None:
		continue


	#for la in tree.nodes:
	#	if la.name == OUTPUT_NAME:
	#		resize_arena(la.rect.width, la.rect.height)
	#		if WORKSPACE:
	#			for lb in la.nodes:
	#				if la.name == WORKSPACE:
	#					curr_workspace = 
	#		else:
	#			curr_workspace = la.find_by_id(la.focus[0]) # .current_workspace doesn't exist in this library??
	#		break

	yeeted = dict(windows)
	for c in curr_workspace.floating_nodes:
		if c.id not in windows:
			create_body(c.id)
		else:
			sync_body(c.id)
		yeeted.pop(c.id, None)

	for i in yeeted:
		destroy_body(i)

	#print("\n" * (len(windows)+1) + f"\x1b[{len(windows)+1}A")
	#print(windows)

	killed = []
	for k, i in windows.items():
		e = i["body"].position
		xt = int((e.x / BOX2D_SCALE) - i["width"]/2)
		yt = int(arena_size[1] - (e.y / BOX2D_SCALE) - i["height"]/2)
		a.command(f"[con_id=\"{k}\"] move absolute position {xt} {yt}")
		a.command(f"[con_id=\"{k}\"] move to workspace \"{curr_workspace.name}\"")

		if not (
			xt - arena_offset[0] > -i["width"]  and xt < arena_size[0] and
			yt - arena_offset[1]> i["height"] - ARENA_HEIGHT/BOX2D_SCALE and yt < arena_size[1]):
			if OOB_BEHAVIOUR == DuckOOBBehaviour.CLOSE:
				a.command(f"[con_id=\"{k}\"] kill")
				killed.append(k)
			elif OOB_BEHAVIOUR == DuckOOBBehaviour.RESPAWN:
				destroy_body(k)
				create_body(k, True)
		if yt < i["height"] - ARENA_DISCARD_HEIGHT/BOX2D_SCALE:
			a.command(f"[con_id=\"{k}\"] kill")
			killed.append(k)

		i["px"] = i["x"]
		i["py"] = i["y"]
		i["x"] = xt
		i["y"] = yt

	#for i in killed:
	#	destroy_body(i)

	#if len(windows) > 0:
	#	b = next(iter(windows.values()))["body"]
	#	b.position = (arena_size[0]/2*BOX2D_SCALE, arena_size[1]/2*BOX2D_SCALE)
	#	b.linearVelocity = (0, 0)
	#	b.mass = 200

	if STATUS:
		print("\x1b[H", end="")

		for k, i in windows.items():
			b = i["body"]
			e = b.position
			ms = b.mass
			print(f"{k:> 4} | "
				f"{e.x:> 9.02f} {e.y:> 9.02f} | {i['x']:> 5} {i['y']:> 5} | {ms: 5.03f}"
				+ "\x1b[K")
		print("\x1b[K", flush=True)

		for i0, i1, e in cl3.collisions:
			print(f"{i0:>4}, {i1:>4} imp={e}\x1b[K")

		print("\x1b[K", flush=True)


	if GRAV != 0: # if this is 0 all forces would be 0 anyway
		# apply newtonian gravity
		win_array = [*windows.values()]
		for j in range(len(win_array)-1):
			dj = win_array[j]
			bj = dj["body"]
			pj = bj.worldCenter
			mj = bj.mass
			for k in range(j+1, len(win_array)):
				dk = win_array[k]
				bk = dk["body"]
				pk = bk.worldCenter
				mk = bk.mass

				dl = (pj - pk)
				r = (pj - pk).Normalize()
				if r != 0:
					f = GRAV * mj * mk / (r*r)

					bj.ApplyForce(-f * dl, pj, True)
					bk.ApplyForce( f * dl, pk, True)
					print(f"{bj.userData['id']:> 4},{bk.userData['id']:> 4} {f}")


	cl3.collisions.clear()
	arena.Step(d, 10, 10)

#bo = [arena.CreateDynamicBody(
#	position=(randrange(BOX_SIZE[0]/2*BOX2D_SCALE, (ARENA_SIZE[0]-BOX_SIZE[0]/2)*BOX2D_SCALE), (ARENA_SIZE[1] + 300 + i*2*BOX_SIZE[1]) * BOX2D_SCALE),
#	linearVelocity=(randrange(-32, 32), randrange(-8, 8)),
#	linearDamping = 0,
#	fixtures=b2.fixtureDef(
#		shape=b2.polygonShape(box=(BOX_SIZE[0]/2*BOX2D_SCALE, BOX_SIZE[1]/2*BOX2D_SCALE)),
#		restitution=1),
#	userData={"index": i} ) for i in range(INSTANCES)]

#for a in bo:




