from OpenGL.GL import *
from OpenGL.GLUT import *
from OpenGL.GLU import *
import math
import random
import time
import heapq

WINDOW_WIDTH, WINDOW_HEIGHT = 1000, 800
GRID_LENGTH = 1000
WALL_HEIGHT = 180.0

last_time = time.perf_counter()
dawn_timer = 100.0
game_over = False
win_state = False
status_msg = "Sneak around, collect 3 of EACH part (Gears, Springs, Hands), and assemble 3 clocks!"
msg_timer = 5.0

# Player physics & state
player_x = 0.0
player_y = -600.0
player_z = 0.0
player_vx = 0.0
player_vy = 0.0
player_vz = 0.0
player_yaw = 90.0
player_pitch = 0.0
is_crouching = False
is_hidden = False
is_on_furniture = False
noise_level = 0.0

# Inventory & Objectives
inventory = {'gear': 0, 'spring': 0, 'hand': 0}
clocks_assembled = 0
TARGET_CLOCKS = 3
workbench_step = 1

# Camera modes & controls
first_person = False
cheat_mode = False
camera_dist = 220.0
camera_height = 120.0

# Distraction Projectiles & Confetti
distraction_gears = []
confetti_particles = []

# Cheat mode throw cooldown and pathing
cheat_throw_cooldown = 0.0
cheat_path = []
cheat_target_pos = None

INITIAL_ITEM_POSITIONS = [
    {'type': 'gear', 'x': -600, 'y': -300, 'z': 25},
    {'type': 'gear', 'x': 600, 'y': -300, 'z': 25},
    {'type': 'gear', 'x': -400, 'y': 400, 'z': 25},
    {'type': 'spring', 'x': 500, 'y': 500, 'z': 25},
    {'type': 'spring', 'x': -700, 'y': 100, 'z': 25},
    {'type': 'spring', 'x': 700, 'y': -100, 'z': 25},
    {'type': 'hand', 'x': 0, 'y': 700, 'z': 25},
    {'type': 'hand', 'x': -300, 'y': -700, 'z': 25},
    {'type': 'hand', 'x': 300, 'y': -700, 'z': 25},
]

items = [
    {'type': cfg['type'], 'x': cfg['x'], 'y': cfg['y'], 'z': cfg['z'], 'collected': False, 'respawn_timer': 0.0}
    for cfg in INITIAL_ITEM_POSITIONS
]

WORKBENCH_X, WORKBENCH_Y = 0.0, 300.0

furniture = [
    {'x': 0, 'y': 300, 'w': 180, 'd': 100, 'h': 55, 'is_hiding': True},
    {'x': -550, 'y': 0, 'w': 120, 'd': 120, 'h': 50, 'is_hiding': True},
    {'x': 550, 'y': 0, 'w': 120, 'd': 120, 'h': 50, 'is_hiding': True},
    {'x': 400, 'y': -400, 'w': 160, 'd': 90, 'h': 45, 'is_hiding': True},
    {'x': -400, 'y': -400, 'w': 160, 'd': 90, 'h': 45, 'is_hiding': True},
]

guards = [
    {
        'x': -500.0, 'y': -200.0, 'z': 0.0,
        'yaw': 0.0, 'state': 0, 'suspicion': 0.0,
        'target_x': None, 'target_y': None,
        'patrol_change_timer': 0.0, 'distraction_timer': 0.0
    },
    {
        'x': 500.0, 'y': 200.0, 'z': 0.0,
        'yaw': 180.0, 'state': 0, 'suspicion': 0.0,
        'target_x': None, 'target_y': None,
        'patrol_change_timer': 0.0, 'distraction_timer': 0.0
    }
]

quadric = None
GRID_SIZE = 50
GRID_DIM = 40

def rad(deg):
    return deg * math.pi / 180.0

def deg(radians):
    return radians * 180.0 / math.pi

def dist2d(x1, y1, x2, y2):
    return math.sqrt((x1 - x2)**2 + (y1 - y2)**2)

def normalize2d(x, y):
    d = math.sqrt(x*x + y*y)
    if d == 0:
        return 0.0, 0.0
    return x / d, y / d

def has_all_required_parts():
    return inventory['gear'] >= 3 and inventory['spring'] >= 3 and inventory['hand'] >= 3

def is_pos_detected_by_guard(px, py):
    for g in guards:
        d = dist2d(px, py, g['x'], g['y'])
        if d < 320.0:
            angle_to_pos = deg(math.atan2(py - g['y'], px - g['x'])) % 360
            angle_diff = abs((angle_to_pos - g['yaw'] + 180) % 360 - 180)
            if angle_diff < 50.0 or d < 90.0:
                return True
    return False

def pick_random_floor_target():
    while True:
        rx = random.uniform(-850, 850)
        ry = random.uniform(-850, 850)
        blocked = False
        for f in furniture:
            if abs(rx - f['x']) < f['w']/2.0 + 50.0 and abs(ry - f['y']) < f['d']/2.0 + 50.0:
                blocked = True
                break
        if not blocked:
            return rx, ry

def world_to_grid(x, y):
    gx = int((x + 1000) // GRID_SIZE)
    gy = int((y + 1000) // GRID_SIZE)
    return max(0, min(GRID_DIM - 1, gx)), max(0, min(GRID_DIM - 1, gy))

def grid_to_world(gx, gy):
    return -1000 + gx * GRID_SIZE + GRID_SIZE / 2.0, -1000 + gy * GRID_SIZE + GRID_SIZE / 2.0

def is_cell_blocked(gx, gy, extra_margin=45.0):
    cx, cy = grid_to_world(gx, gy)
    if abs(cx) > 950 or abs(cy) > 950:
        return True
    for f in furniture:
        if (f['x'] - f['w']/2.0 - extra_margin <= cx <= f['x'] + f['w']/2.0 + extra_margin and
            f['y'] - f['d']/2.0 - extra_margin <= cy <= f['y'] + f['d']/2.0 + extra_margin):
            return True
    return False

def get_cell_cost(gx, gy):
    if is_cell_blocked(gx, gy):
        return float('inf')
    cx, cy = grid_to_world(gx, gy)
    cost = 1.0
    for g in guards:
        d = dist2d(cx, cy, g['x'], g['y'])
        if d < 350.0:
            ang = deg(math.atan2(cy - g['y'], cx - g['x'])) % 360
            angle_diff = abs((ang - g['yaw'] + 180) % 360 - 180)
            if angle_diff < 45.0 or d < 100.0:
                cost += 500.0
    return cost

def find_path_astar(start_w, target_w):
    sgx, sgy = world_to_grid(start_w[0], start_w[1])
    tgx, tgy = world_to_grid(target_w[0], target_w[1])

    if sgx == tgx and sgy == tgy:
        return [target_w]

    open_set = []
    heapq.heappush(open_set, (0, (sgx, sgy)))
    came_from = {}
    g_score = {(sgx, sgy): 0}

    neighbors = [
        (1, 0, 1.0), (-1, 0, 1.0), (0, 1, 1.0), (0, -1, 1.0),
        (1, 1, 1.414), (-1, 1, 1.414), (1, -1, 1.414), (-1, -1, 1.414)
    ]

    while open_set:
        _, current = heapq.heappop(open_set)
        if current == (tgx, tgy):
            path = []
            curr = current
            while curr in came_from:
                path.append(grid_to_world(curr[0], curr[1]))
                curr = came_from[curr]
            path.reverse()
            path.append(target_w)
            return path

        for dx, dy, step_cost in neighbors:
            nx, ny = current[0] + dx, current[1] + dy
            if 0 <= nx < GRID_DIM and 0 <= ny < GRID_DIM:
                if dx != 0 and dy != 0:
                    if is_cell_blocked(current[0] + dx, current[1]) or is_cell_blocked(current[0], current[1] + dy):
                        continue

                cell_penalty = get_cell_cost(nx, ny)
                if cell_penalty == float('inf'):
                    continue

                tentative_g = g_score[current] + step_cost * cell_penalty
                if tentative_g < g_score.get((nx, ny), float('inf')):
                    came_from[(nx, ny)] = current
                    g_score[(nx, ny)] = tentative_g
                    h = math.sqrt((nx - tgx)**2 + (ny - tgy)**2)
                    heapq.heappush(open_set, (tentative_g + h, (nx, ny)))

    return [target_w]

def check_furniture_collision(px, py, radius=20.0):
    for f in furniture:
        min_x = f['x'] - f['w'] / 2.0 - radius
        max_x = f['x'] + f['w'] / 2.0 + radius
        min_y = f['y'] - f['d'] / 2.0 - radius
        max_y = f['y'] + f['d'] / 2.0 + radius
        if player_z < f['h'] - 5.0:
            if min_x <= px <= max_x and min_y <= py <= max_y:
                return True, f
    return False, None

def line_intersects_box(x1, y1, x2, y2, bx, by, bw, bd):
    min_x, max_x = bx - bw / 2.0, bx + bw / 2.0
    min_y, max_y = by - bd / 2.0, by + bd / 2.0
    steps = 15
    for i in range(1, steps):
        t = i / float(steps)
        px = x1 + t * (x2 - x1)
        py = y1 + t * (y2 - y1)
        if min_x <= px <= max_x and min_y <= py <= max_y:
            return True
    return False

def reset_game():
    global player_x, player_y, player_z, player_vx, player_vy, player_vz, player_yaw, player_pitch
    global is_crouching, is_hidden, is_on_furniture, noise_level, inventory, clocks_assembled, workbench_step
    global dawn_timer, game_over, win_state, status_msg, distraction_gears, items, guards, last_time
    global cheat_throw_cooldown, cheat_path, cheat_target_pos, confetti_particles

    player_x, player_y, player_z = 0.0, -600.0, 0.0
    player_vx, player_vy, player_vz = 0.0, 0.0, 0.0
    player_yaw, player_pitch = 90.0, 0.0
    is_crouching = False
    is_hidden = False
    is_on_furniture = False
    noise_level = 0.0
    cheat_throw_cooldown = 0.0
    cheat_path = []
    cheat_target_pos = None

    inventory = {'gear': 0, 'spring': 0, 'hand': 0}
    clocks_assembled = 0
    workbench_step = 1

    dawn_timer = 100.0
    game_over = False
    win_state = False
    status_msg = "Collect 3 Gears, 3 Springs, and 3 Hands, then assemble 3 clocks at Workbench!"
    distraction_gears.clear()
    confetti_particles.clear()

    for idx, item in enumerate(items):
        item['collected'] = False
        item['respawn_timer'] = 0.0
        item['x'] = INITIAL_ITEM_POSITIONS[idx]['x']
        item['y'] = INITIAL_ITEM_POSITIONS[idx]['y']

    for g in guards:
        tx, ty = pick_random_floor_target()
        g['state'], g['suspicion'], g['distraction_timer'] = 0, 0.0, 0.0
        g['target_x'], g['target_y'] = tx, ty
        g['patrol_change_timer'] = random.uniform(5.0, 10.0)

    guards[0]['x'], guards[0]['y'], guards[0]['yaw'] = -500.0, -200.0, 0.0
    guards[1]['x'], guards[1]['y'], guards[1]['yaw'] = 500.0, 200.0, 180.0

    last_time = time.perf_counter()

def draw_background_quad(r, g, b):
    glMatrixMode(GL_PROJECTION)
    glPushMatrix()
    glLoadIdentity()
    gluOrtho2D(0, WINDOW_WIDTH, 0, WINDOW_HEIGHT)

    glMatrixMode(GL_MODELVIEW)
    glPushMatrix()
    glLoadIdentity()

    glColor3f(r, g, b)
    glBegin(GL_QUADS)
    glVertex2f(0, 0)
    glVertex2f(WINDOW_WIDTH, 0)
    glVertex2f(WINDOW_WIDTH, WINDOW_HEIGHT)
    glVertex2f(0, WINDOW_HEIGHT)
    glEnd()

    glPopMatrix()
    glMatrixMode(GL_PROJECTION)
    glPopMatrix()
    glMatrixMode(GL_MODELVIEW)

def update_and_draw_confetti(dt):
    global confetti_particles
    if not win_state:
        confetti_particles.clear()
        return

    cx, cy = WINDOW_WIDTH / 2.0, WINDOW_HEIGHT / 2.0
    for _ in range(12):
        angle = random.uniform(0, 2 * math.pi)
        speed = random.uniform(250.0, 750.0)
        confetti_particles.append({
            'x': cx,
            'y': cy,
            'vx': math.cos(angle) * speed,
            'vy': math.sin(angle) * speed + random.uniform(-100, 200),
            'length': random.uniform(15.0, 40.0),
            'r': random.random(),
            'g': random.random(),
            'b': random.random(),
            'life': random.uniform(1.0, 2.2)
        })

    glMatrixMode(GL_PROJECTION)
    glPushMatrix()
    glLoadIdentity()
    gluOrtho2D(0, WINDOW_WIDTH, 0, WINDOW_HEIGHT)

    glMatrixMode(GL_MODELVIEW)
    glPushMatrix()
    glLoadIdentity()

    glLineWidth(3.0)
    glBegin(GL_LINES)
    survived = []
    for p in confetti_particles:
        p['x'] += p['vx'] * dt
        p['y'] += p['vy'] * dt
        p['vy'] -= 350.0 * dt
        p['life'] -= dt

        if p['life'] > 0 and 0 <= p['x'] <= WINDOW_WIDTH and 0 <= p['y'] <= WINDOW_HEIGHT:
            glColor3f(p['r'], p['g'], p['b'])
            v_mag = math.sqrt(p['vx']**2 + p['vy']**2)
            if v_mag > 0:
                dx = (p['vx'] / v_mag) * p['length']
                dy = (p['vy'] / v_mag) * p['length']
            else:
                dx, dy = 0, p['length']
            glVertex2f(p['x'], p['y'])
            glVertex2f(p['x'] - dx, p['y'] - dy)
            survived.append(p)
    glEnd()

    confetti_particles = survived

    glPopMatrix()
    glMatrixMode(GL_PROJECTION)
    glPopMatrix()
    glMatrixMode(GL_MODELVIEW)

def draw_text(x, y, text, font=GLUT_BITMAP_HELVETICA_18, r=1.0, g=1.0, b=1.0):
    glColor3f(r, g, b)
    glMatrixMode(GL_PROJECTION)
    glPushMatrix()
    glLoadIdentity()
    gluOrtho2D(0, WINDOW_WIDTH, 0, WINDOW_HEIGHT)

    glMatrixMode(GL_MODELVIEW)
    glPushMatrix()
    glLoadIdentity()

    glRasterPos2f(x, y)
    for ch in text:
        glutBitmapCharacter(font, ord(ch))

    glPopMatrix()
    glMatrixMode(GL_PROJECTION)
    glPopMatrix()
    glMatrixMode(GL_MODELVIEW)

def draw_objective_arrow():
    if not has_all_required_parts():
        needed_types = [t for t in ['gear', 'spring', 'hand'] if inventory[t] < 3]
        uncollected = [it for it in items if not it['collected'] and it['type'] in needed_types]
        if uncollected:
            target_obj = min(uncollected, key=lambda it: dist2d(player_x, player_y, it['x'], it['y']))
            tx, ty = target_obj['x'], target_obj['y']
        else:
            tx, ty = WORKBENCH_X, WORKBENCH_Y
    else:
        tx, ty = WORKBENCH_X, WORKBENCH_Y

    angle_to_target = deg(math.atan2(ty - player_y, tx - player_x))

    glPushMatrix()
    arrow_height = player_z + (70 if is_crouching else 105) + math.sin(time.perf_counter() * 5.0) * 4.0
    glTranslatef(player_x, player_y, arrow_height)
    glRotatef(angle_to_target, 0, 0, 1)

    glColor3f(0.1, 1.0, 0.9)
    glPushMatrix()
    glRotatef(90, 0, 1, 0)
    gluCylinder(quadric, 2.5, 2.5, 20, 8, 8)
    glPopMatrix()

    glColor3f(1.0, 0.9, 0.2)
    glPushMatrix()
    glTranslatef(20, 0, 0)
    glRotatef(90, 0, 1, 0)
    gluCylinder(quadric, 7.0, 0.0, 15, 8, 8)
    glPopMatrix()
    glPopMatrix()

def draw_gnome():
    global quadric
    if quadric is None:
        quadric = gluNewQuadric()

    draw_objective_arrow()

    glPushMatrix()
    z_offset = player_z + (15 if is_crouching else 30)
    glTranslatef(player_x, player_y, z_offset)
    glRotatef(player_yaw - 90, 0, 0, 1)

    if is_crouching:
        glScalef(1.0, 1.0, 0.65)

    glColor3f(0.1, 0.15, 0.55)
    glPushMatrix()
    gluCylinder(quadric, 20, 14, 45, 12, 12)
    glPopMatrix()

    glColor3f(0.95, 0.75, 0.65)
    glPushMatrix()
    glTranslatef(0, 0, 52)
    gluSphere(quadric, 16, 12, 12)
    glPopMatrix()

    glColor3f(0.9, 0.1, 0.1)
    glPushMatrix()
    glTranslatef(0, 0, 62)
    gluCylinder(quadric, 17, 0, 35, 12, 12)
    glPopMatrix()

    glColor3f(0.1, 0.15, 0.55)
    glPushMatrix()
    glTranslatef(-22, 0, 30)
    glRotatef(20, 0, 1, 0)
    gluCylinder(quadric, 5, 5, 22, 8, 8)
    glColor3f(0.95, 0.75, 0.65)
    glTranslatef(0, 0, 22)
    gluSphere(quadric, 6, 8, 8)
    glPopMatrix()

    glColor3f(0.1, 0.15, 0.55)
    glPushMatrix()
    glTranslatef(22, 0, 30)
    glRotatef(-20, 0, 1, 0)
    gluCylinder(quadric, 5, 5, 22, 8, 8)
    glColor3f(0.95, 0.75, 0.65)
    glTranslatef(0, 0, 22)
    gluSphere(quadric, 6, 8, 8)
    glPopMatrix()

    glColor3f(0.1, 0.15, 0.55)
    glPushMatrix()
    glTranslatef(-10, 0, -25)
    gluCylinder(quadric, 6, 6, 25, 8, 8)
    glColor3f(0.85, 0.1, 0.1)
    glTranslatef(0, 5, 2)
    glScalef(0.4, 0.7, 0.3)
    glutSolidCube(30)
    glPopMatrix()

    glColor3f(0.1, 0.15, 0.55)
    glPushMatrix()
    glTranslatef(10, 0, -25)
    gluCylinder(quadric, 6, 6, 25, 8, 8)
    glColor3f(0.85, 0.1, 0.1)
    glTranslatef(0, 5, 2)
    glScalef(0.4, 0.7, 0.3)
    glutSolidCube(30)
    glPopMatrix()

    glPopMatrix()

def draw_guard(guard):
    global quadric
    if quadric is None:
        quadric = gluNewQuadric()

    glPushMatrix()
    glTranslatef(guard['x'], guard['y'], guard['z'] + 40)
    glRotatef(guard['yaw'] - 90, 0, 0, 1)

    if guard['state'] == 2:
        body_r, body_g, body_b = 1.0, 0.0, 0.0
    elif guard['state'] == 1:
        body_r, body_g, body_b = 0.9, 0.7, 0.1
    else:
        body_r, body_g, body_b = 0.8, 0.15, 0.15

    glColor3f(body_r, body_g, body_b)
    glPushMatrix()
    glScalef(1.2, 0.9, 1.8)
    glutSolidCube(40)
    glPopMatrix()

    glColor3f(0.3, 0.3, 0.35)
    glPushMatrix()
    glTranslatef(0, 0, 48)
    gluSphere(quadric, 14, 10, 10)
    glColor3f(1.0, 0.2, 0.0) if guard['state'] == 2 else glColor3f(0.0, 1.0, 0.5)
    glTranslatef(0, 10, 3)
    gluSphere(quadric, 4, 8, 8)
    glPopMatrix()

    glColor3f(body_r, body_g, body_b)
    glPushMatrix()
    glTranslatef(-30, 0, 10)
    glRotatef(90, 1, 0, 0)
    gluCylinder(quadric, 8, 8, 35, 8, 8)
    glPopMatrix()

    glPushMatrix()
    glTranslatef(30, 0, 10)
    glRotatef(90, 1, 0, 0)
    gluCylinder(quadric, 8, 8, 35, 8, 8)
    glPopMatrix()

    glPushMatrix()
    glTranslatef(-16, 0, -40)
    gluCylinder(quadric, 10, 8, 40, 8, 8)
    glPopMatrix()

    glPushMatrix()
    glTranslatef(16, 0, -40)
    gluCylinder(quadric, 10, 8, 40, 8, 8)
    glPopMatrix()

    glPopMatrix()

    glPushMatrix()
    glTranslatef(guard['x'], guard['y'], 2.0)
    fov_half = 45.0
    cone_dist = 300.0
    guard_angle = guard['yaw']

    if guard['state'] == 2:
        glColor3f(1.0, 0.1, 0.1)
    elif guard['state'] == 1:
        glColor3f(1.0, 0.8, 0.2)
    else:
        glColor3f(0.2, 0.8, 0.3)

    glLineWidth(2.0)
    glBegin(GL_LINES)
    a1 = rad(guard_angle - fov_half)
    glVertex3f(0, 0, 0)
    glVertex3f(math.cos(a1) * cone_dist, math.sin(a1) * cone_dist, 0)

    a2 = rad(guard_angle + fov_half)
    glVertex3f(0, 0, 0)
    glVertex3f(math.cos(a2) * cone_dist, math.sin(a2) * cone_dist, 0)

    steps = 14
    for i in range(steps):
        ta1 = rad(guard_angle - fov_half + (i * (2 * fov_half / steps)))
        ta2 = rad(guard_angle - fov_half + ((i + 1) * (2 * fov_half / steps)))
        glVertex3f(math.cos(ta1) * cone_dist, math.sin(ta1) * cone_dist, 0)
        glVertex3f(math.cos(ta2) * cone_dist, math.sin(ta2) * cone_dist, 0)
    glEnd()
    glPopMatrix()

def draw_item(item):
    if item['collected']:
        return

    global quadric
    if quadric is None:
        quadric = gluNewQuadric()

    t = time.perf_counter()
    glPushMatrix()
    bob = math.sin(t * 4.0) * 5.0
    glTranslatef(item['x'], item['y'], item['z'] + bob)

    glPushMatrix()
    glRotatef(t * 120.0, 0, 0, 1)
    glLineWidth(2.5)
    glColor3f(1.0, 0.85, 0.2)
    
    glBegin(GL_LINES)
    ring_radius = 28.0 + math.sin(t * 6.0) * 4.0
    num_pts = 20
    for i in range(num_pts):
        ang1 = rad(i * (360.0 / num_pts))
        ang2 = rad(((i + 1) % num_pts) * (360.0 / num_pts))
        glVertex3f(math.cos(ang1) * ring_radius, math.sin(ang1) * ring_radius, 0.0)
        glVertex3f(math.cos(ang2) * ring_radius, math.sin(ang2) * ring_radius, 0.0)
    glEnd()

    glRotatef(45.0 + t * 90.0, 1, 0, 0)
    glColor3f(0.2, 0.9, 1.0)
    glBegin(GL_LINES)
    num_pts2 = 16
    for i in range(num_pts2):
        ang1 = rad(i * (360.0 / num_pts2))
        ang2 = rad(((i + 1) % num_pts2) * (360.0 / num_pts2))
        glVertex3f(math.cos(ang1) * 22.0, math.sin(ang1) * 22.0, math.sin(ang1 * 2) * 5.0)
        glVertex3f(math.cos(ang2) * 22.0, math.sin(ang2) * 22.0, math.sin(ang2 * 2) * 5.0)
    glEnd()
    glPopMatrix()

    glRotatef(t * 60.0, 0, 0, 1)
    if item['type'] == 'gear':
        glColor3f(0.95, 0.84, 0.15)
        gluCylinder(quadric, 18, 18, 8, 12, 1)
        for tooth_angle in range(0, 360, 45):
            glPushMatrix()
            glRotatef(tooth_angle, 0, 0, 1)
            glTranslatef(18, 0, 4)
            glScalef(0.3, 0.3, 0.3)
            glutSolidCube(15)
            glPopMatrix()

    elif item['type'] == 'spring':
        glColor3f(0.75, 0.8, 0.85)
        for coil in range(4):
            glPushMatrix()
            glTranslatef(0, 0, coil * 7)
            gluCylinder(quadric, 12, 12, 4, 10, 1)
            glPopMatrix()

    elif item['type'] == 'hand':
        glColor3f(0.9, 0.2, 0.1)
        glScalef(0.3, 1.8, 0.2)
        glutSolidCube(25)

    glPopMatrix()

def draw_environment():
    global quadric
    if quadric is None:
        quadric = gluNewQuadric()

    glColor3f(0.0, 0.0, 0.0)
    glBegin(GL_QUADS)
    glVertex3f(-GRID_LENGTH, -GRID_LENGTH, -0.1)
    glVertex3f(GRID_LENGTH, -GRID_LENGTH, -0.1)
    glVertex3f(GRID_LENGTH, GRID_LENGTH, -0.1)
    glVertex3f(-GRID_LENGTH, GRID_LENGTH, -0.1)
    glEnd()

    tile_step = 100
    tile_radius = 46.0
    segments = 16

    for x in range(-GRID_LENGTH + 50, GRID_LENGTH, tile_step):
        for y in range(-GRID_LENGTH + 50, GRID_LENGTH, tile_step):
            shade = ((x // tile_step) + (y // tile_step)) % 3
            if shade == 0:
                glColor3f(0.12, 0.12, 0.14)
            elif shade == 1:
                glColor3f(0.25, 0.25, 0.28)
            else:
                glColor3f(0.38, 0.38, 0.42)

            glBegin(GL_TRIANGLES)
            for i in range(segments):
                ang1 = rad(i * (360.0 / segments))
                ang2 = rad((i + 1) * (360.0 / segments))
                glVertex3f(x, y, 0.0)
                glVertex3f(x + math.cos(ang1) * tile_radius, y + math.sin(ang1) * tile_radius, 0.0)
                glVertex3f(x + math.cos(ang2) * tile_radius, y + math.sin(ang2) * tile_radius, 0.0)
            glEnd()

    glColor3f(0.12, 0.1, 0.14)
    glBegin(GL_QUADS)
    glVertex3f(-GRID_LENGTH, GRID_LENGTH, 0)
    glVertex3f(GRID_LENGTH, GRID_LENGTH, 0)
    glVertex3f(GRID_LENGTH, GRID_LENGTH, WALL_HEIGHT)
    glVertex3f(-GRID_LENGTH, GRID_LENGTH, WALL_HEIGHT)

    glVertex3f(-GRID_LENGTH, -GRID_LENGTH, 0)
    glVertex3f(GRID_LENGTH, -GRID_LENGTH, 0)
    glVertex3f(GRID_LENGTH, -GRID_LENGTH, WALL_HEIGHT)
    glVertex3f(-GRID_LENGTH, -GRID_LENGTH, WALL_HEIGHT)

    glVertex3f(-GRID_LENGTH, -GRID_LENGTH, 0)
    glVertex3f(-GRID_LENGTH, GRID_LENGTH, 0)
    glVertex3f(-GRID_LENGTH, GRID_LENGTH, WALL_HEIGHT)
    glVertex3f(-GRID_LENGTH, -GRID_LENGTH, WALL_HEIGHT)

    glVertex3f(GRID_LENGTH, -GRID_LENGTH, 0)
    glVertex3f(GRID_LENGTH, GRID_LENGTH, 0)
    glVertex3f(GRID_LENGTH, GRID_LENGTH, WALL_HEIGHT)
    glVertex3f(GRID_LENGTH, -GRID_LENGTH, WALL_HEIGHT)
    glEnd()

    for f in furniture:
        if f['is_hiding']:
            glColor3f(0.05, 0.05, 0.08)
            glBegin(GL_QUADS)
            glVertex3f(f['x'] - f['w']/2 - 15, f['y'] - f['d']/2 - 15, 0.5)
            glVertex3f(f['x'] + f['w']/2 + 15, f['y'] - f['d']/2 - 15, 0.5)
            glVertex3f(f['x'] + f['w']/2 + 15, f['y'] + f['d']/2 + 15, 0.5)
            glVertex3f(f['x'] - f['w']/2 - 15, f['y'] + f['d']/2 + 15, 0.5)
            glEnd()

        glPushMatrix()
        glTranslatef(f['x'], f['y'], f['h']/2)
        glScalef(f['w']/40.0, f['d']/40.0, f['h']/40.0)
        glColor3f(0.45, 0.25, 0.12)
        glutSolidCube(40)
        glPopMatrix()

    glPushMatrix()
    glTranslatef(WORKBENCH_X, WORKBENCH_Y, 60)
    glColor3f(0.1, 0.4, 0.8)
    glBegin(GL_QUADS)
    glVertex3f(-60, -35, 1)
    glVertex3f(60, -35, 1)
    glVertex3f(60, 35, 1)
    glVertex3f(-60, 35, 1)
    glEnd()

    for c in range(clocks_assembled):
        glPushMatrix()
        glTranslatef(-40 + c * 40, 0, 15)
        glColor3f(0.95, 0.84, 0.15)
        gluSphere(quadric, 12, 10, 10)
        glPopMatrix()
    glPopMatrix()

    for d in distraction_gears:
        glPushMatrix()
        glTranslatef(d['x'], d['y'], d['z'])
        glRotatef(time.perf_counter() * 300.0, 1, 1, 0)
        glColor3f(0.95, 0.84, 0.15)
        gluCylinder(quadric, 10, 10, 5, 8, 1)
        glPopMatrix()

def setupCamera():
    global first_person, player_x, player_y, player_z, player_yaw, player_pitch, camera_dist, camera_height, is_crouching
    glMatrixMode(GL_PROJECTION)
    glLoadIdentity()
    gluPerspective(75.0, WINDOW_WIDTH / float(WINDOW_HEIGHT), 1.0, 3000.0)

    glMatrixMode(GL_MODELVIEW)
    glLoadIdentity()

    if first_person:
        eye_z = player_z + (20 if is_crouching else 45)
        look_x = player_x + math.cos(rad(player_yaw)) * math.cos(rad(player_pitch)) * 200.0
        look_y = player_y + math.sin(rad(player_yaw)) * math.cos(rad(player_pitch)) * 200.0
        look_z = eye_z + math.sin(rad(player_pitch)) * 200.0
        gluLookAt(player_x, player_y, eye_z, look_x, look_y, look_z, 0, 0, 1)
    else:
        cam_x = player_x - math.cos(rad(player_yaw)) * camera_dist
        cam_y = player_y - math.sin(rad(player_yaw)) * camera_dist
        cam_z = player_z + camera_height

        cam_margin = 40.0
        cam_x = max(-GRID_LENGTH + cam_margin, min(GRID_LENGTH - cam_margin, cam_x))
        cam_y = max(-GRID_LENGTH + cam_margin, min(GRID_LENGTH - cam_margin, cam_y))
        cam_z = max(15.0, min(WALL_HEIGHT - 10.0, cam_z))

        gluLookAt(cam_x, cam_y, cam_z, player_x, player_y, player_z + 30.0, 0, 0, 1)

def throw_any_item(override_yaw=None):
    global status_msg, msg_timer

    thrown_type = None
    for item_t in ['gear', 'spring', 'hand']:
        if inventory[item_t] > 0:
            thrown_type = item_t
            break

    if thrown_type is None:
        status_msg = "No parts in inventory to throw!"
        msg_timer = 2.5
        return False

    inventory[thrown_type] -= 1
    use_yaw = player_yaw if override_yaw is None else override_yaw

    throw_speed = 320.0
    distraction_gears.append({
        'type': thrown_type,
        'x': player_x,
        'y': player_y,
        'z': player_z + 30.0,
        'vx': math.cos(rad(use_yaw)) * throw_speed,
        'vy': math.sin(rad(use_yaw)) * throw_speed,
        'vz': 180.0,
        'landed': False,
        'noise_timer': 0.0
    })
    status_msg = f"Threw a {thrown_type.capitalize()}!"
    msg_timer = 3.0
    return True

def mouseListener(button, state, x, y):
    global first_person

    if state == GLUT_DOWN:
        if button == GLUT_RIGHT_BUTTON:
            first_person = not first_person
        elif button == GLUT_LEFT_BUTTON and not game_over and not win_state:
            throw_any_item()

def keyboardListener(key, x, y):
    global player_vx, player_vy, player_vz, is_crouching, cheat_mode, cheat_path, cheat_target_pos
    global status_msg, msg_timer

    k = key.lower()

    if k == b'r':
        reset_game()
        return

    if game_over or win_state:
        return

    gnome_speed = 550.0 if cheat_mode else (250.0 if is_crouching else 550.0)

    if k == b'w':
        player_vx = math.cos(rad(player_yaw)) * gnome_speed
        player_vy = math.sin(rad(player_yaw)) * gnome_speed
    elif k == b's':
        player_vx = -math.cos(rad(player_yaw)) * gnome_speed
        player_vy = -math.sin(rad(player_yaw)) * gnome_speed
    elif k == b'a':
        player_vx = math.cos(rad(player_yaw + 90)) * gnome_speed
        player_vy = math.sin(rad(player_yaw + 90)) * gnome_speed
    elif k == b'd':
        player_vx = math.cos(rad(player_yaw - 90)) * gnome_speed
        player_vy = math.sin(rad(player_yaw - 90)) * gnome_speed
    elif k == b' ':
        if player_z <= 0.1 or any(abs(player_z - f['h']) < 3.0 for f in furniture):
            player_vz = 340.0
            is_crouching = False
    elif k == b'c':
        is_crouching = not is_crouching
    elif k == b'p':
        cheat_mode = not cheat_mode
        if not cheat_mode:
            cheat_path = []
            cheat_target_pos = None
        else:
            status_msg = "CHEAT MODE: Auto-Nav collecting 3 of EACH part!"
            msg_timer = 3.0
    elif k == b'e':
        check_workbench_interaction()

def specialKeyListener(key, x, y):
    global player_yaw, player_pitch, camera_height

    if game_over or win_state:
        return

    if key == GLUT_KEY_LEFT:
        player_yaw += 2.0
    elif key == GLUT_KEY_RIGHT:
        player_yaw -= 2.0
    elif key == GLUT_KEY_UP:
        player_pitch = min(60.0, player_pitch + 1.5)
        camera_height = min(300.0, camera_height + 3.0)
    elif key == GLUT_KEY_DOWN:
        player_pitch = max(-40.0, player_pitch - 1.5)
        camera_height = max(60.0, camera_height - 3.0)

def check_workbench_interaction():
    global workbench_step, clocks_assembled, win_state, status_msg, msg_timer

    d = dist2d(player_x, player_y, WORKBENCH_X, WORKBENCH_Y)
    if d < 140.0:
        req_type = 'gear' if workbench_step == 1 else ('spring' if workbench_step == 2 else 'hand')
        if inventory[req_type] > 0:
            inventory[req_type] -= 1
            workbench_step += 1
            if workbench_step > 3:
                clocks_assembled += 1
                workbench_step = 1
                status_msg = f"SUCCESS! Clock #{clocks_assembled} assembled!"
                msg_timer = 4.0
                if clocks_assembled >= TARGET_CLOCKS:
                    win_state = True
            else:
                status_msg = f"Installed {req_type.capitalize()} on Workbench! Next: {('Spring' if workbench_step==2 else 'Hand')}."
                msg_timer = 2.5
        else:
            status_msg = f"Workbench requires a {req_type.capitalize()} for step #{workbench_step}!"
            msg_timer = 2.5

def idle():
    global last_time, dawn_timer, game_over, win_state, player_x, player_y, player_z
    global player_vx, player_vy, player_vz, is_hidden, is_on_furniture, noise_level
    global status_msg, msg_timer, workbench_step, is_crouching, player_yaw, player_pitch, camera_height
    global cheat_throw_cooldown, inventory, clocks_assembled, cheat_path, cheat_target_pos

    current_time = time.perf_counter()
    dt = current_time - last_time
    last_time = current_time

    if dt > 0.05:
        dt = 0.05

    if game_over or win_state:
        glutPostRedisplay()
        return

    gravity = -750.0
    was_in_air = player_z > 0.1 and not any(abs(player_z - f['h']) < 3.0 for f in furniture)
    player_vz += gravity * dt
    player_z += player_vz * dt

    on_surface = False
    if player_z <= 0.0:
        player_z = 0.0
        player_vz = 0.0
        on_surface = True

    for f in furniture:
        if abs(player_x - f['x']) <= (f['w']/2 + 10) and abs(player_y - f['y']) <= (f['d']/2 + 10):
            if player_z <= f['h'] and (player_z - player_vz * dt) >= f['h'] - 10.0:
                player_z = f['h']
                player_vz = 0.0
                on_surface = True
                break

    if was_in_air and on_surface:
        noise_level = min(100.0, noise_level + 60.0)

    cur_spd = math.sqrt(player_vx**2 + player_vy**2)

    next_x = player_x + player_vx * dt
    next_y = player_y + player_vy * dt

    collided_x, _ = check_furniture_collision(next_x, player_y, radius=22.0)
    if not collided_x and -GRID_LENGTH + 20 < next_x < GRID_LENGTH - 20:
        player_x = next_x
    else:
        player_vx = 0.0

    collided_y, _ = check_furniture_collision(player_x, next_y, radius=22.0)
    if not collided_y and -GRID_LENGTH + 20 < next_y < GRID_LENGTH - 20:
        player_y = next_y
    else:
        player_vy = 0.0

    if not cheat_mode:
        damping = math.exp(-6.5 * dt)
        player_vx *= damping
        player_vy *= damping

    dawn_timer -= dt
    if dawn_timer <= 0.0:
        dawn_timer = 0.0
        game_over = True
        status_msg = "DAWN ARRIVED! You ran out of time!"

    if msg_timer > 0:
        msg_timer -= dt

    for item in items:
        if not item['collected']:
            if dist2d(player_x, player_y, item['x'], item['y']) < 40.0 and abs(player_z - item['z']) < 40.0:
                item['collected'] = True
                item['respawn_timer'] = 2.0
                inventory[item['type']] += 1
                status_msg = f"Picked up {item['type'].capitalize()}! (Gears:{inventory['gear']}/3, Springs:{inventory['spring']}/3, Hands:{inventory['hand']}/3)"
                msg_timer = 2.5
        else:
            if item['respawn_timer'] > 0.0:
                item['respawn_timer'] -= dt
                if item['respawn_timer'] <= 0.0:
                    rx, ry = pick_random_floor_target()
                    item['x'] = rx
                    item['y'] = ry
                    item['collected'] = False
                    item['respawn_timer'] = 0.0

    is_on_furniture = False
    for f in furniture:
        if abs(player_x - f['x']) <= (f['w']/2 + 10) and abs(player_y - f['y']) <= (f['d']/2 + 10):
            if player_z >= f['h'] - 5.0:
                is_on_furniture = True
                break

    is_hidden = False
    for f in furniture:
        if f['is_hiding']:
            if abs(player_x - f['x']) < (f['w']/2 + 10) and abs(player_y - f['y']) < (f['d']/2 + 10):
                if is_crouching and player_z <= f['h']:
                    is_hidden = True
                    break

    if cheat_mode:
        is_crouching = False

        if not has_all_required_parts():
            needed_types = [t for t in ['gear', 'spring', 'hand'] if inventory[t] < 3]
            uncollected_needed = [it for it in items if not it['collected'] and it['type'] in needed_types]
            
            if uncollected_needed:
                safe_candidates = [it for it in uncollected_needed if not is_pos_detected_by_guard(it['x'], it['y'])]
                if safe_candidates:
                    target_item = min(safe_candidates, key=lambda it: dist2d(player_x, player_y, it['x'], it['y']))
                else:
                    target_item = min(uncollected_needed, key=lambda it: dist2d(player_x, player_y, it['x'], it['y']))
                
                desired_target = (target_item['x'], target_item['y'])
            else:
                desired_target = (WORKBENCH_X, WORKBENCH_Y - 80.0)
        else:
            desired_target = (WORKBENCH_X, WORKBENCH_Y - 80.0)

        if cheat_target_pos != desired_target or not cheat_path:
            cheat_target_pos = desired_target
            cheat_path = find_path_astar((player_x, player_y), cheat_target_pos)

        if cheat_path:
            next_node = cheat_path[0]
            dist_to_node = dist2d(player_x, player_y, next_node[0], next_node[1])
            if dist_to_node < 25.0:
                cheat_path.pop(0)
                if cheat_path:
                    next_node = cheat_path[0]

            if cheat_path:
                dx, dy = next_node[0] - player_x, next_node[1] - player_y
                ndx, ndy = normalize2d(dx, dy)
                cheat_speed = 850.0
                player_vx = ndx * cheat_speed
                player_vy = ndy * cheat_speed

        if has_all_required_parts() and dist2d(player_x, player_y, WORKBENCH_X, WORKBENCH_Y) < 140.0:
            for _ in range(9):
                req_type = 'gear' if workbench_step == 1 else ('spring' if workbench_step == 2 else 'hand')
                if inventory[req_type] > 0 and clocks_assembled < TARGET_CLOCKS:
                    check_workbench_interaction()
                else:
                    break

    if cur_spd > 15.0 and not is_crouching:
        noise_level = min(100.0, noise_level + 22.0 * dt)
    elif is_crouching:
        noise_level = max(0.0, noise_level - 35.0 * dt)
    else:
        noise_level = max(0.0, noise_level - 15.0 * dt)

    g_grav = -650.0
    for d in distraction_gears:
        if not d['landed']:
            d['x'] += d['vx'] * dt
            d['y'] += d['vy'] * dt
            d['vz'] += g_grav * dt
            d['z'] += d['vz'] * dt
            if d['z'] <= 0.0:
                d['z'] = 0.0
                d['landed'] = True
                d['noise_timer'] = 2.5

                for g_obj in guards:
                    if dist2d(g_obj['x'], g_obj['y'], d['x'], d['y']) < 600.0:
                        g_obj['state'] = 1
                        g_obj['suspicion'] = 80.0
                        g_obj['target_x'] = d['x']
                        g_obj['target_y'] = d['y']
                        g_obj['distraction_timer'] = 4.0
        else:
            d['noise_timer'] -= dt

    distraction_gears[:] = [d for d in distraction_gears if d['noise_timer'] > 0 or not d['landed']]

    for guard in guards:
        d_player = dist2d(guard['x'], guard['y'], player_x, player_y)
        line_blocked = any(line_intersects_box(guard['x'], guard['y'], player_x, player_y, f['x'], f['y'], f['w'], f['d']) for f in furniture)

        if d_player < 45.0 and guard['state'] == 2 and not cheat_mode:
            if not is_hidden and not is_on_furniture and not line_blocked and abs(player_z - guard['z']) < 35.0:
                game_over = True
                status_msg = "CAUGHT! A guard spotted and captured you!"
                return

        if noise_level >= 95.0 and d_player < 400.0:
            guard['state'] = 1
            guard['suspicion'] = min(100.0, guard['suspicion'] + dt * 200.0)
            guard['target_x'], guard['target_y'] = player_x, player_y
            if guard['suspicion'] >= 100.0:
                guard['state'] = 2

        if guard['distraction_timer'] > 0:
            guard['distraction_timer'] -= dt
            gdx, gdy = guard['target_x'] - guard['x'], guard['target_y'] - guard['y']
            if dist2d(guard['x'], guard['y'], guard['target_x'], guard['target_y']) > 15.0:
                g_ndx, g_ndy = normalize2d(gdx, gdy)
                guard['x'] += g_ndx * 100.0 * dt
                guard['y'] += g_ndy * 100.0 * dt
                guard['yaw'] = deg(math.atan2(g_ndy, g_ndx))
            continue

        angle_to_player = deg(math.atan2(player_y - guard['y'], player_x - guard['x'])) % 360
        angle_diff = abs((angle_to_player - guard['yaw'] + 180) % 360 - 180)

        can_see = (d_player < 300.0 and angle_diff < 45.0 and not is_hidden and not is_on_furniture and not line_blocked)

        if can_see:
            guard['suspicion'] += dt * 140.0
            if guard['suspicion'] >= 100.0:
                guard['state'] = 2
                guard['target_x'], guard['target_y'] = player_x, player_y
            elif guard['state'] == 0:
                guard['state'] = 1
                guard['target_x'], guard['target_y'] = player_x, player_y
        else:
            guard['suspicion'] = max(0.0, guard['suspicion'] - dt * 120.0)
            if guard['suspicion'] <= 0.0 and guard['distraction_timer'] <= 0:
                guard['state'] = 0

        base_speed = 200.0 if guard['state'] == 2 else 150.0
        g_speed = (70.0 if guard['state'] == 2 else 50.0) if cheat_mode else base_speed

        if guard['state'] in (1, 2):
            gdx, gdy = guard['target_x'] - guard['x'], guard['target_y'] - guard['y']
            if dist2d(guard['x'], guard['y'], guard['target_x'], guard['target_y']) > 10.0:
                g_ndx, g_ndy = normalize2d(gdx, gdy)
                guard['x'] += g_ndx * g_speed * dt
                guard['y'] += g_ndy * g_speed * dt
                guard['yaw'] = deg(math.atan2(g_ndy, g_ndx))
        else:
            guard['patrol_change_timer'] -= dt
            if (guard['target_x'] is None or
                dist2d(guard['x'], guard['y'], guard['target_x'], guard['target_y']) < 25.0 or
                guard['patrol_change_timer'] <= 0.0):
                
                guard['target_x'], guard['target_y'] = pick_random_floor_target()
                guard['patrol_change_timer'] = random.uniform(6.0, 12.0)

            gdx, gdy = guard['target_x'] - guard['x'], guard['target_y'] - guard['y']
            g_ndx, g_ndy = normalize2d(gdx, gdy)
            guard['x'] += g_ndx * g_speed * dt
            guard['y'] += g_ndy * g_speed * dt
            guard['yaw'] = deg(math.atan2(g_ndy, g_ndx))

    glutPostRedisplay()

def draw_hud_noise_bar(x, y, width, height, noise_val):
    glMatrixMode(GL_PROJECTION)
    glPushMatrix()
    glLoadIdentity()
    gluOrtho2D(0, WINDOW_WIDTH, 0, WINDOW_HEIGHT)

    glMatrixMode(GL_MODELVIEW)
    glPushMatrix()
    glLoadIdentity()

    glColor3f(0.8, 0.8, 0.8)
    glLineWidth(2.0)
    glBegin(GL_LINES)
    glVertex2f(x, y)
    glVertex2f(x + width, y)

    glVertex2f(x + width, y)
    glVertex2f(x + width, y + height)

    glVertex2f(x + width, y + height)
    glVertex2f(x, y + height)

    glVertex2f(x, y + height)
    glVertex2f(x, y)
    glEnd()

    fill_w = (max(0.0, min(100.0, noise_val)) / 100.0) * (width - 4)

    if noise_val < 40.0:
        r, g, b = 0.2, 0.9, 0.3
    elif noise_val < 75.0:
        r, g, b = 0.9, 0.8, 0.1
    else:
        r, g, b = 1.0, 0.2, 0.1

    glColor3f(r, g, b)
    glBegin(GL_QUADS)
    glVertex2f(x + 2, y + 2)
    glVertex2f(x + 2 + fill_w, y + 2)
    glVertex2f(x + 2 + fill_w, y + height - 2)
    glVertex2f(x + 2, y + height - 2)
    glEnd()

    glPopMatrix()
    glMatrixMode(GL_PROJECTION)
    glPopMatrix()
    glMatrixMode(GL_MODELVIEW)

def showScreen():
    glClear(GL_DEPTH_BUFFER_BIT)

    t_ratio = max(0.0, min(1.0, dawn_timer / 100.0))
    sky_r = t_ratio * 0.02 + (1.0 - t_ratio) * 0.90
    sky_g = t_ratio * 0.05 + (1.0 - t_ratio) * 0.32
    sky_b = t_ratio * 0.25 + (1.0 - t_ratio) * 0.12
    draw_background_quad(sky_r, sky_g, sky_b)

    glViewport(0, 0, WINDOW_WIDTH, WINDOW_HEIGHT)
    setupCamera()

    draw_environment()
    for item in items:
        draw_item(item)
    for guard in guards:
        draw_guard(guard)

    if not first_person:
        draw_gnome()

    glViewport(WINDOW_WIDTH - 220, WINDOW_HEIGHT - 220, 200, 200)
    glMatrixMode(GL_PROJECTION)
    glPushMatrix()
    glLoadIdentity()
    glOrtho(-1100.0, 1100.0, -1100.0, 1100.0, 10.0, 3000.0)

    glMatrixMode(GL_MODELVIEW)
    glPushMatrix()
    glLoadIdentity()
    gluLookAt(0.0, 0.0, 1500.0, 0.0, 0.0, 0.0, 0, 1, 0)

    glColor3f(0.12, 0.12, 0.14)
    glBegin(GL_QUADS)
    glVertex3f(-GRID_LENGTH, -GRID_LENGTH, 0.0)
    glVertex3f(GRID_LENGTH, -GRID_LENGTH, 0.0)
    glVertex3f(GRID_LENGTH, GRID_LENGTH, 0.0)
    glVertex3f(-GRID_LENGTH, GRID_LENGTH, 0.0)
    glEnd()

    for f in furniture:
        glPushMatrix()
        glTranslatef(f['x'], f['y'], 5.0)
        glScalef(f['w']/40.0, f['d']/40.0, 1.0)
        glColor3f(0.45, 0.25, 0.12)
        glutSolidCube(40)
        glPopMatrix()

    for item in items:
        if not item['collected']:
            glPushMatrix()
            glTranslatef(item['x'], item['y'], 20)
            glColor3f(1.0, 0.85, 0.0)
            gluSphere(quadric, 40, 8, 8)
            glPopMatrix()

    glPushMatrix()
    glTranslatef(player_x, player_y, 20)
    glColor3f(0.0, 1.0, 0.3)
    gluSphere(quadric, 40, 8, 8)
    glPopMatrix()

    for g_obj in guards:
        glPushMatrix()
        glTranslatef(g_obj['x'], g_obj['y'], 20)
        glColor3f(1.0, 0.0, 0.0)
        gluSphere(quadric, 40, 8, 8)
        glPopMatrix()

    glPopMatrix()
    glMatrixMode(GL_PROJECTION)
    glPopMatrix()
    glMatrixMode(GL_MODELVIEW)

    glViewport(0, 0, WINDOW_WIDTH, WINDOW_HEIGHT)

    draw_text(20, 770, "THE CLOCKMAKER'S APPRENTICE", font=GLUT_BITMAP_HELVETICA_18, r=1.0, g=0.9, b=0.3)
    draw_text(20, 740, f"Clocks Assembled: {clocks_assembled} / {TARGET_CLOCKS}", r=0.4, g=1.0, b=0.4)
    draw_text(20, 715, f"Parts: Gears ({inventory['gear']}/3) | Springs ({inventory['spring']}/3) | Hands ({inventory['hand']}/3)", r=0.9, g=0.9, b=0.9)
    draw_text(20, 690, f"Dawn Countdown: {dawn_timer:.1f}s", r=1.0, g=0.5, b=0.2)
    draw_text(20, 665, f"Camera Mode: {'FIRST PERSON (FPS)' if first_person else 'THIRD PERSON (TPS)'}", r=0.7, g=0.8, b=1.0)

    stealth_str = "HIDDEN (FURNITURE)" if (is_hidden or is_on_furniture) else ("CROUCHING" if is_crouching else "RUNNING")
    stealth_r, stealth_g, stealth_b = (0.3, 1.0, 0.3) if (is_hidden or is_on_furniture) else ((0.9, 0.9, 0.3) if is_crouching else (1.0, 0.5, 0.5))
    draw_text(20, 640, f"Stealth Status: {stealth_str}", r=stealth_r, g=stealth_g, b=stealth_b)

    draw_text(20, 615, "Noise Level:", r=0.9, g=0.9, b=0.9)
    draw_hud_noise_bar(120, 615, 160, 16, noise_level)

    if cheat_mode:
        draw_text(20, 585, "CHEAT AUTO-NAVIGATE: ACTIVE", r=1.0, g=0.2, b=0.8)

    if status_msg:
        draw_text(20, 555, f">> {status_msg}", r=1.0, g=1.0, b=0.2)

    draw_text(20, 90, "CONTROLS: WASD=Move | SPACE=Jump | C=Crouch/Hide | E=Assemble at Workbench", r=0.7, g=0.7, b=0.7)
    draw_text(20, 65, "LEFT CLICK=Throw Inventory Item | RIGHT CLICK=Toggle FPS/TPS | ARROWS=Look", r=0.7, g=0.7, b=0.7)
    draw_text(20, 40, "P=Toggle Cheat Auto-Nav | R=Reset", r=0.7, g=0.7, b=0.7)

    if win_state:
        update_and_draw_confetti(0.016)
        draw_text(300, 430, "VICTORY! All Clocks Assembled Before Dawn!", font=GLUT_BITMAP_HELVETICA_18, r=0.2, g=1.0, b=0.3)
        draw_text(380, 390, "Press R to play again", font=GLUT_BITMAP_HELVETICA_18, r=1.0, g=1.0, b=1.0)
    elif game_over:
        draw_text(320, 430, "GAME OVER!", font=GLUT_BITMAP_HELVETICA_18, r=1.0, g=0.2, b=0.2)
        draw_text(300, 390, status_msg, font=GLUT_BITMAP_HELVETICA_18, r=1.0, g=0.8, b=0.2)
        draw_text(370, 350, "Press R to Restart", font=GLUT_BITMAP_HELVETICA_18, r=1.0, g=1.0, b=1.0)

    glutSwapBuffers()

def main():
    glutInit()
    glutInitDisplayMode(GLUT_DOUBLE | GLUT_RGB | GLUT_DEPTH)
    glutInitWindowSize(WINDOW_WIDTH, WINDOW_HEIGHT)
    glutInitWindowPosition(50, 50)
    glutCreateWindow(b"The Clockmaker's Apprentice - CSE423 3D Project")

    glutDisplayFunc(showScreen)
    glutKeyboardFunc(keyboardListener)
    glutSpecialFunc(specialKeyListener)
    glutMouseFunc(mouseListener)
    glutIdleFunc(idle)

    reset_game()
    glutMainLoop()

if __name__ == "__main__":
    main()