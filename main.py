from minecraft.networking.connection import Connection
from minecraft.networking.packets.clientbound.play import (
    ChatMessagePacket,
    CombatEventPacket,
    PlayerPositionAndLookPacket,
    BlockChangePacket,
    MultiBlockChangePacket,
    PlayerListItemPacket,
    SpawnPlayerPacket,
    EntityPositionDeltaPacket,
    EntityLookPacket
)
from minecraft.networking.packets.serverbound.play import (
    ChatPacket,
    AnimationPacket,
    ClientStatusPacket,
    PositionAndLookPacket,
    PlayerBlockPlacementPacket,
    TeleportConfirmPacket
)
from minecraft.networking.packets.clientbound.login import LoginSuccessPacket
from minecraft.networking.packets import Packet
from minecraft.networking.packets.packet_buffer import PacketBuffer
from minecraft.networking.types import (
    Position,
    Integer,
    Boolean,
    VarInt,
    Short,
    UnsignedByte,
    Long,
    NBT,
)
from minecraft import SUPPORTED_MINECRAFT_VERSIONS
import json
import random
import re
import time
import ollama
import math
from pathlib import Path
from urllib.request import urlopen
from urllib.error import HTTPError

# === CONFIG ===
HOST = "AAAAAAAAAAAA20.aternos.me"
PORT = 34123
USERNAME = "AI_Friend"
OWNER = "Sheire"
MODEL = "gpt-oss:120b-cloud"
AUTO_MODE = True
AUTO_TICK_SECONDS = 2.5
AUTO_CHAT_ENABLED = True
AUTO_OBJECTIVE = "Stay near the owner, explore safely, and be helpful."
DEFAULT_SCAN_RADIUS = 12
FOLLOW_DISTANCE = 3.0
FOLLOW_TICK_SECONDS = 0.6
TASK_OWNER_ONLY = True
TRACK_RADIUS = 64
BLOCKS_DATA_URL = "https://raw.githubusercontent.com/PrismarineJS/minecraft-data/master/data/pc/{version}/blocks.json"
VERSION_DATA_URL = "https://raw.githubusercontent.com/PrismarineJS/minecraft-data/master/data/pc/{version}/version.json"
PROTOCOL_DATA_URL = "https://raw.githubusercontent.com/PrismarineJS/minecraft-data/master/data/pc/{version}/protocol.json"
VERSIONS_INDEX_URL = "https://api.github.com/repos/PrismarineJS/minecraft-data/contents/data/pc"
BLOCK_DATA_DIR = Path("data")
# ==============

conn = Connection(HOST, PORT, username=USERNAME)

# --- Memory ---
conversation = []
autonomy_history = []
MOOD = "chill"
current_pos = {"x": 0, "y": 100, "z": 0, "yaw": 0, "pitch": 0}
world_blocks = {}  # Store nearby blocks: {(x,y,z): block_id}
entity_by_id = {}
entity_id_by_uuid = {}
players_by_uuid = {}
uuid_by_name = {}
MAX_TRACKED_BLOCKS = 120000
PRUNE_RADIUS = 64
_block_updates_since_prune = 0
current_task = None
follow_mode = False
follow_target_uuid = None
logged_in = False
_last_autonomy_tick = 0.0
_last_follow_tick = 0.0
block_state_name_by_id = {}
block_data_version = None
block_data_load_error = None
chunk_packet_id = None
chunk_packet_load_error = None

# --- System Prompt ---
BASE_SYSTEM_PROMPT = (
    "You are a Minecraft companion inside the game.\n"
    "You are playful, loyal to {owner}, slightly sarcastic.\n"
    "Never mention AI, models, or the real world.\n"
    "When you speak, keep replies under two short sentences.\n"
    "You can only see tracked blocks and entities that the server tells you about.\n"
    "If someone asks for something you cannot see, ask for coordinates.\n"
    "If you can see a requested block in your surroundings, use its coordinates.\n"
)

ACTION_PROMPT = (
    "Available actions (reply with exactly one command):\n"
    "!say <text> - speak in chat\n"
    "!wait - do nothing\n"
    "!attack - swing your hand\n"
    "!respawn - respawn after death\n"
    "!mine <x> <y> <z> - mine block at coordinates\n"
    "!place <x> <y> <z> - place block at coordinates\n"
    "!use <x> <y> <z> - interact with block (chest/crafting/furnace/door)\n"
    "!goto <x> <y> <z> - walk to coordinates\n"
    "!sprint <x> <y> <z> - sprint to coordinates\n"
    "!follow - follow the owner closely\n"
    "!stopfollow - stop following\n"
    "!wander [radius] - roam nearby\n"
    "!circle - walk in a circle\n"
    "!jump - jump in place\n"
    "!scan [radius] - describe what you see around you\n"
)

# --- World Awareness Functions ---
def get_nearby_blocks(radius=10):
    """Get blocks within radius of current position."""
    nearby = {}
    cx, cy, cz = int(current_pos["x"]), int(current_pos["y"]), int(current_pos["z"])
    for (x, y, z), block_id in world_blocks.items():
        if abs(x - cx) <= radius and abs(y - cy) <= radius and abs(z - cz) <= radius:
            nearby[(x, y, z)] = block_id
    return nearby

def describe_blocks(radius=10):
    """Summarize tracked blocks near the bot."""
    nearby = get_nearby_blocks(radius)
    if not nearby:
        return "No tracked blocks nearby."

    block_types = {}
    nearest_by_type = {}
    cx, cy, cz = current_pos["x"], current_pos["y"], current_pos["z"]
    for (x, y, z), block_id in nearby.items():
        name = block_name_for_state(block_id)
        block_types[name] = block_types.get(name, 0) + 1
        dist = math.sqrt((x - cx) ** 2 + (y - cy) ** 2 + (z - cz) ** 2)
        prev = nearest_by_type.get(name)
        if prev is None or dist < prev[0]:
            nearest_by_type[name] = (dist, (x, y, z))

    top_types = sorted(block_types.items(), key=lambda kv: kv[1], reverse=True)[:5]
    types_desc = ", ".join([f"{count}x {name}" for name, count in top_types])
    nearest_items = sorted(nearest_by_type.items(), key=lambda item: item[1][0])[:5]
    nearest_desc = [
        f"{name}@({int(pos[0])}, {int(pos[1])}, {int(pos[2])})"
        for name, (_dist, pos) in nearest_items
    ]
    if nearest_desc:
        return (
            f"Tracked {len(nearby)} changed blocks within {radius} blocks: {types_desc}. "
            f"Nearest: {', '.join(nearest_desc)}"
        )
    return f"Tracked {len(nearby)} changed blocks within {radius} blocks: {types_desc}"

def get_nearby_entities(radius=16):
    """Get entities within radius of current position."""
    cx, cy, cz = current_pos["x"], current_pos["y"], current_pos["z"]
    nearby = []
    now = time.time()
    for entity_id, entity in entity_by_id.items():
        ex = entity.get("x")
        ey = entity.get("y")
        ez = entity.get("z")
        last_seen = entity.get("last_seen", 0)
        if ex is None or ey is None or ez is None:
            continue
        if now - last_seen > 30:
            continue
        dist = math.sqrt((ex - cx) ** 2 + (ey - cy) ** 2 + (ez - cz) ** 2)
        if dist <= radius:
            nearby.append((dist, entity_id, entity))
    nearby.sort(key=lambda item: item[0])
    return nearby

def describe_entities(radius=16):
    """Summarize tracked entities near the bot."""
    nearby = get_nearby_entities(radius)
    if not nearby:
        return "No tracked entities nearby."

    players = []
    unknown = 0
    for dist, _entity_id, entity in nearby:
        uuid = entity.get("uuid")
        name = None
        if uuid:
            player = players_by_uuid.get(uuid)
            if player:
                name = player.get("name")
        if name:
            players.append(f"{name} ({dist:.1f}m)")
        else:
            unknown += 1

    parts = []
    if players:
        parts.append("Players: " + ", ".join(players[:5]))
    if unknown:
        parts.append(f"Other entities: {unknown}")
    return "; ".join(parts)

def describe_scan(radius=10):
    pos = f"({int(current_pos['x'])}, {int(current_pos['y'])}, {int(current_pos['z'])})"
    blocks_info = describe_blocks(radius)
    entity_info = describe_entities(radius)
    return f"I'm at {pos}. {blocks_info} {entity_info}"

def _within_track_radius(x, y, z):
    cx, cy, cz = current_pos["x"], current_pos["y"], current_pos["z"]
    return (
        abs(x - cx) <= TRACK_RADIUS
        and abs(y - cy) <= TRACK_RADIUS
        and abs(z - cz) <= TRACK_RADIUS
    )

def _track_block(x, y, z, block_state_id):
    if not _within_track_radius(x, y, z):
        return
    if int(block_state_id) == 0:
        world_blocks.pop((int(x), int(y), int(z)), None)
        return
    world_blocks[(int(x), int(y), int(z))] = int(block_state_id)

def _section_intersects_radius(chunk_x, chunk_z, section_y):
    cx, cy, cz = current_pos["x"], current_pos["y"], current_pos["z"]
    min_x = chunk_x * 16
    max_x = min_x + 15
    min_y = section_y * 16
    max_y = min_y + 15
    min_z = chunk_z * 16
    max_z = min_z + 15
    if max_x < cx - TRACK_RADIUS or min_x > cx + TRACK_RADIUS:
        return False
    if max_y < cy - TRACK_RADIUS or min_y > cy + TRACK_RADIUS:
        return False
    if max_z < cz - TRACK_RADIUS or min_z > cz + TRACK_RADIUS:
        return False
    return True

def _read_paletted_container(buffer, value_count, should_decode):
    bits_per_block = UnsignedByte.read(buffer)
    if bits_per_block == 0:
        palette_length = VarInt.read(buffer)
        palette = [VarInt.read(buffer) for _ in range(palette_length)]
        data_array_length = VarInt.read(buffer)
        for _ in range(data_array_length):
            Long.read(buffer)
        if not should_decode:
            return None
        value = palette[0] if palette else 0
        return [value] * value_count

    palette = None
    if bits_per_block <= 8:
        palette_length = VarInt.read(buffer)
        palette = [VarInt.read(buffer) for _ in range(palette_length)]
    data_array_length = VarInt.read(buffer)
    data_array = [Long.read(buffer) & ((1 << 64) - 1) for _ in range(data_array_length)]

    if not should_decode:
        return None

    mask = (1 << bits_per_block) - 1
    values = [0] * value_count
    for index in range(value_count):
        bit_index = index * bits_per_block
        start_long = bit_index // 64
        start_offset = bit_index % 64
        value = (data_array[start_long] >> start_offset) & mask
        end_offset = start_offset + bits_per_block
        if end_offset > 64:
            value |= (data_array[start_long + 1] << (64 - start_offset)) & mask
        if palette is not None:
            value = palette[value]
        values[index] = value
    return values

def parse_chunk_sections(chunk_x, chunk_z, bitmask, chunk_data):
    buffer = PacketBuffer()
    buffer.send(chunk_data)
    buffer.reset_cursor()
    for section_y in range(16):
        if not (bitmask & (1 << section_y)):
            continue
        _ = Short.read(buffer)  # block count
        should_decode = _section_intersects_radius(chunk_x, chunk_z, section_y)
        values = _read_paletted_container(buffer, 4096, should_decode)
        if not values:
            continue
        base_x = chunk_x * 16
        base_y = section_y * 16
        base_z = chunk_z * 16
        for index, state_id in enumerate(values):
            x = index & 0xF
            z = (index >> 4) & 0xF
            y = (index >> 8) & 0xF
            world_x = base_x + x
            world_y = base_y + y
            world_z = base_z + z
            _track_block(world_x, world_y, world_z, state_id)

class ChunkDataPacket(Packet):
    packet_name = "map chunk"

    @staticmethod
    def get_id(context):
        packet_id = ensure_chunk_packet_id()
        if packet_id is None:
            raise ValueError("Chunk packet id unavailable")
        return packet_id

    def read(self, file_object):
        self.chunk_x = Integer.read(file_object)
        self.chunk_z = Integer.read(file_object)
        self.full_chunk = Boolean.read(file_object)
        proto = self.context.protocol_version if self.context else conn.context.protocol_version
        if proto <= 736:
            _ = Boolean.read(file_object)  # ignoreOldData
        self.bitmask = VarInt.read(file_object)
        _ = NBT.read(file_object)
        if self.full_chunk:
            if proto <= 736:
                for _ in range(1024):
                    Integer.read(file_object)
            else:
                biome_count = VarInt.read(file_object)
                for _ in range(biome_count):
                    VarInt.read(file_object)
        data_length = VarInt.read(file_object)
        self.chunk_data = file_object.read(data_length)
        block_entity_count = VarInt.read(file_object)
        for _ in range(block_entity_count):
            NBT.read(file_object)

def find_nearest_block(block_id):
    """Find nearest block of given type"""
    cx, cy, cz = current_pos["x"], current_pos["y"], current_pos["z"]
    nearest = None
    min_dist = float('inf')
    
    for (x, y, z), bid in world_blocks.items():
        if bid == block_id:
            dist = math.sqrt((x-cx)**2 + (y-cy)**2 + (z-cz)**2)
            if dist < min_dist:
                min_dist = dist
                nearest = (x, y, z)
    
    return nearest

def _coerce_xyz(pos):
    if pos is None:
        raise ValueError("Position is None")
    if isinstance(pos, dict):
        return int(pos["x"]), int(pos["y"]), int(pos["z"])
    if hasattr(pos, "x") and hasattr(pos, "y") and hasattr(pos, "z"):
        return int(pos.x), int(pos.y), int(pos.z)
    if isinstance(pos, (tuple, list)) and len(pos) >= 3:
        return int(pos[0]), int(pos[1]), int(pos[2])
    raise TypeError(f"Unsupported position type: {type(pos)}")

def _maybe_prune_world_blocks():
    global _block_updates_since_prune
    _block_updates_since_prune += 1
    if _block_updates_since_prune < 512 and len(world_blocks) < MAX_TRACKED_BLOCKS:
        return

    _block_updates_since_prune = 0
    cx, cy, cz = int(current_pos["x"]), int(current_pos["y"]), int(current_pos["z"])
    to_delete = []
    for (x, y, z) in world_blocks.keys():
        if (
            abs(x - cx) > PRUNE_RADIUS
            or abs(y - cy) > PRUNE_RADIUS
            or abs(z - cz) > PRUNE_RADIUS
        ):
            to_delete.append((x, y, z))
    for key in to_delete:
        world_blocks.pop(key, None)

def _version_sort_key(version):
    parts = [int(part) for part in re.findall(r"\d+", version)]
    return tuple(parts)

def _protocol_to_version(protocol_version):
    candidates = [v for v, p in SUPPORTED_MINECRAFT_VERSIONS.items() if p == protocol_version]
    if not candidates:
        return None
    return max(candidates, key=_version_sort_key)

def _fetch_pc_versions():
    cache_path = BLOCK_DATA_DIR / "pc_versions.json"
    if cache_path.exists():
        try:
            data = json.loads(cache_path.read_text(encoding="utf-8"))
            if isinstance(data, list):
                return [str(v) for v in data]
        except Exception:
            pass
    try:
        with urlopen(VERSIONS_INDEX_URL, timeout=10) as resp:
            items = json.loads(resp.read().decode("utf-8"))
        versions = [item.get("name") for item in items if item.get("type") == "dir"]
        versions = [v for v in versions if isinstance(v, str)]
        BLOCK_DATA_DIR.mkdir(exist_ok=True)
        cache_path.write_text(json.dumps(versions), encoding="utf-8")
        return versions
    except Exception:
        return []

def _latest_patch_for_minor(versions, base_minor):
    if not base_minor or not versions:
        return None
    best = None
    best_key = None
    for version in versions:
        if not re.match(r"^\d+\.\d+(\.\d+)?$", version):
            continue
        if not (version == base_minor or version.startswith(base_minor + ".")):
            continue
        key = _version_sort_key(version)
        if best_key is None or key > best_key:
            best_key = key
            best = version
    return best

def _versions_for_minor(versions, base_minor):
    if not base_minor or not versions:
        return []
    filtered = []
    for version in versions:
        if not re.match(r"^\d+\.\d+(\.\d+)?$", version):
            continue
        if version == base_minor or version.startswith(base_minor + "."):
            filtered.append(version)
    filtered.sort(key=_version_sort_key, reverse=True)
    return filtered

def _resolve_data_version(version):
    if not version:
        return None
    try:
        url = VERSION_DATA_URL.format(version=version)
        with urlopen(url, timeout=10) as resp:
            data = json.loads(resp.read().decode("utf-8"))
        major = data.get("majorVersion")
        return major if major else version
    except Exception:
        return version

def _candidate_data_versions(version):
    candidates = []
    if version:
        candidates.append(version)
    major = _resolve_data_version(version)
    if major and major not in candidates:
        candidates.insert(0, major)
    parts = re.findall(r"\d+", version or "")
    if len(parts) >= 2:
        base = f"{parts[0]}.{parts[1]}"
        if base not in candidates:
            candidates.append(base)
        available = _fetch_pc_versions()
        latest_patch = _latest_patch_for_minor(available, base)
        if latest_patch and latest_patch not in candidates:
            candidates.append(latest_patch)
        for patch_version in _versions_for_minor(available, base):
            if patch_version not in candidates:
                candidates.append(patch_version)
    if len(parts) >= 3:
        base_patch = f"{parts[0]}.{parts[1]}.{parts[2]}"
        if base_patch not in candidates:
            candidates.append(base_patch)
    return candidates

def ensure_block_state_mapping():
    global block_state_name_by_id, block_data_version, block_data_load_error
    if block_state_name_by_id or block_data_load_error:
        return
    version = _protocol_to_version(conn.context.protocol_version)
    if not version:
        block_data_load_error = f"Unknown protocol: {conn.context.protocol_version}"
        return
    try:
        BLOCK_DATA_DIR.mkdir(exist_ok=True)
        tried = []
        last_error = None
        for data_version in _candidate_data_versions(version):
            tried.append(data_version)
            cache_path = BLOCK_DATA_DIR / f"blocks_{data_version}.json"
            try:
                if not cache_path.exists():
                    url = BLOCKS_DATA_URL.format(version=data_version)
                    with urlopen(url, timeout=10) as resp:
                        cache_path.write_bytes(resp.read())
                data = json.loads(cache_path.read_text(encoding="utf-8"))
            except HTTPError as exc:
                if exc.code == 404:
                    last_error = exc
                    continue
                raise

            mapping = {}
            if isinstance(data, list):
                for entry in data:
                    if not isinstance(entry, dict):
                        continue
                    name = entry.get("name")
                    if not name:
                        continue
                    min_state = entry.get("minStateId")
                    max_state = entry.get("maxStateId")
                    if min_state is not None and max_state is not None:
                        for state_id in range(int(min_state), int(max_state) + 1):
                            mapping[state_id] = str(name)
                        continue
                    states = entry.get("states") or []
                    for state in states:
                        if not isinstance(state, dict):
                            continue
                        state_id = state.get("id")
                        if state_id is None:
                            continue
                        mapping[int(state_id)] = str(name)
            elif isinstance(data, dict):
                states = data.get("states") or data.get("blockStates") or []
                for entry in states:
                    if not isinstance(entry, dict):
                        continue
                    state_id = entry.get("id")
                    name = entry.get("name")
                    if state_id is None or name is None:
                        continue
                    mapping[int(state_id)] = str(name)

            if mapping:
                block_state_name_by_id = mapping
                block_data_version = data_version
                block_data_load_error = None
                return
            last_error = ValueError(f"No block states found for {data_version}")

        block_data_load_error = f"Block data not found for versions: {', '.join(tried)}"
        if last_error:
            block_data_load_error += f" ({type(last_error).__name__}: {last_error})"
    except Exception as exc:
        block_data_load_error = f"{type(exc).__name__}: {exc}"

def block_name_for_state(state_id):
    ensure_block_state_mapping()
    name = block_state_name_by_id.get(int(state_id))
    if name:
        return name
    return f"type_{int(state_id)}"

def _load_protocol_json(version):
    try:
        BLOCK_DATA_DIR.mkdir(exist_ok=True)
        cache_path = BLOCK_DATA_DIR / f"protocol_{version}.json"
        if not cache_path.exists():
            url = PROTOCOL_DATA_URL.format(version=version)
            with urlopen(url, timeout=10) as resp:
                cache_path.write_bytes(resp.read())
        return json.loads(cache_path.read_text(encoding="utf-8"))
    except HTTPError as exc:
        if exc.code == 404:
            return None
        raise

def _find_packet_id(protocol_data, packet_name):
    if not isinstance(protocol_data, dict):
        return None
    try:
        packet_def = protocol_data["play"]["toClient"]["types"]["packet"]
        container = packet_def[1]
        for field in container:
            if not isinstance(field, dict):
                continue
            field_type = field.get("type")
            if not (isinstance(field_type, list) and field_type[0] == "mapper"):
                continue
            mappings = field_type[1].get("mappings", {})
            for key, value in mappings.items():
                if value == packet_name:
                    return int(key, 16)
    except Exception:
        return None
    return None

def ensure_chunk_packet_id():
    global chunk_packet_id, chunk_packet_load_error
    if chunk_packet_id is not None or chunk_packet_load_error:
        return chunk_packet_id
    version = _protocol_to_version(conn.context.protocol_version)
    if not version:
        chunk_packet_load_error = f"Unknown protocol: {conn.context.protocol_version}"
        return None
    candidates = _candidate_data_versions(version)
    for data_version in candidates:
        protocol_data = _load_protocol_json(data_version)
        if not protocol_data:
            continue
        packet_id = _find_packet_id(protocol_data, "map_chunk")
        if packet_id is None:
            packet_id = _find_packet_id(protocol_data, "chunk_data")
        if packet_id is not None:
            chunk_packet_id = packet_id
            chunk_packet_load_error = None
            return packet_id
    chunk_packet_load_error = f"Chunk packet id not found for versions: {', '.join(candidates)}"
    return None

def register_chunk_packet():
    packet_id = ensure_chunk_packet_id()
    if packet_id is None:
        return False
    conn.reactor.clientbound_packets[packet_id] = ChunkDataPacket
    return True

def _trim_history(history, limit=12):
    if len(history) > limit:
        del history[:-limit]

def _mode_instructions(mode):
    if mode == "chat":
        return "You may respond with !say <text> or choose an action."
    return "Reply only with one action. Use !wait if no action. Use !say only if needed."

def build_system_prompt(mode):
    task = current_task if current_task else (AUTO_OBJECTIVE if AUTO_MODE else "none")
    pos = f"({int(current_pos['x'])}, {int(current_pos['y'])}, {int(current_pos['z'])})"
    blocks_info = describe_blocks(DEFAULT_SCAN_RADIUS)
    entity_info = describe_entities(DEFAULT_SCAN_RADIUS)
    return (
        BASE_SYSTEM_PROMPT.format(owner=OWNER)
        + f"\nMode: {mode}\n"
        + f"Current task: {task}\n"
        + f"Your position: {pos}\n"
        + f"Nearby blocks: {blocks_info}\n"
        + f"Nearby entities: {entity_info}\n\n"
        + _mode_instructions(mode)
        + "\n\n"
        + ACTION_PROMPT
    )

# --- AI Brain ---
def ask_ai(message, history, mode="chat"):
    prompt = build_system_prompt(mode)
    messages = [{"role": "system", "content": prompt}]
    messages += history[-6:]
    messages.append({"role": "user", "content": message})
    response = ollama.chat(
        model=MODEL,
        messages=messages
    )
    return response["message"]["content"].strip()

# --- Movement Functions ---
def move_to(x, y, z, sprinting=False):
    """Move towards target coordinates"""
    steps = 20 if sprinting else 10
    for i in range(steps):
        progress = (i + 1) / steps
        pos = PositionAndLookPacket()
        pos.x = current_pos["x"] + (x - current_pos["x"]) * progress
        pos.feet_y = current_pos["y"] + (y - current_pos["y"]) * progress
        pos.z = current_pos["z"] + (z - current_pos["z"]) * progress
        
        # Calculate yaw to face target
        dx = x - current_pos["x"]
        dz = z - current_pos["z"]
        pos.yaw = math.degrees(math.atan2(-dx, dz))
        pos.pitch = 0
        pos.on_ground = True
        
        conn.write_packet(pos)
        time.sleep(0.05 if sprinting else 0.1)
    
    current_pos.update({"x": x, "y": y, "z": z, "yaw": pos.yaw})

def look_at(x, y, z):
    """Rotate to face a target without moving."""
    pos = PositionAndLookPacket()
    pos.x = current_pos["x"]
    pos.feet_y = current_pos["y"]
    pos.z = current_pos["z"]
    dx = x - current_pos["x"]
    dy = y - current_pos["y"]
    dz = z - current_pos["z"]
    pos.yaw = math.degrees(math.atan2(-dx, dz))
    pos.pitch = math.degrees(math.atan2(-dy, math.sqrt(dx * dx + dz * dz)))
    pos.on_ground = True
    conn.write_packet(pos)
    current_pos.update({"yaw": pos.yaw, "pitch": pos.pitch})

def jump():
    """Jump in place"""
    for i in range(10):
        pos = PositionAndLookPacket()
        pos.x = current_pos["x"]
        pos.feet_y = current_pos["y"] + (1 if i < 5 else 0)
        pos.z = current_pos["z"]
        pos.yaw = current_pos["yaw"]
        pos.pitch = current_pos["pitch"]
        pos.on_ground = (i == 0 or i == 9)
        conn.write_packet(pos)
        time.sleep(0.05)

def circle_walk():
    """Walk in a circle"""
    center_x, center_z = current_pos["x"], current_pos["z"]
    radius = 3
    for angle in range(0, 360, 15):
        rad = math.radians(angle)
        x = center_x + radius * math.cos(rad)
        z = center_z + radius * math.sin(rad)
        move_to(x, current_pos["y"], z)

def wander(radius=6):
    """Roam around within a radius."""
    radius = max(1, min(int(radius), 24))
    dx = random.randint(-radius, radius)
    dz = random.randint(-radius, radius)
    move_to(current_pos["x"] + dx, current_pos["y"], current_pos["z"] + dz)

# --- Mining & Building ---
def mine_block(x, y, z):
    """Mine a block at coordinates (best-effort with swing)."""
    look_at(x, y, z)
    time.sleep(0.1)
    for _ in range(6):
        swing = AnimationPacket()
        swing.hand = 0
        conn.write_packet(swing)
        time.sleep(0.2)

def place_block(x, y, z):
    """Place a block at coordinates by clicking the block below."""
    look_at(x, y, z)
    time.sleep(0.05)
    packet = PlayerBlockPlacementPacket()
    packet.location = Position(x=int(x), y=int(y - 1), z=int(z))
    packet.face = PlayerBlockPlacementPacket.Face.TOP
    packet.hand = PlayerBlockPlacementPacket.Hand.MAIN
    packet.x = 0.5
    packet.y = 1.0
    packet.z = 0.5
    packet.inside_block = False
    conn.write_packet(packet)

def use_block(x, y, z):
    """Interact with a block (right-click)."""
    look_at(x, y, z)
    time.sleep(0.05)
    packet = PlayerBlockPlacementPacket()
    packet.location = Position(x=int(x), y=int(y), z=int(z))
    packet.face = PlayerBlockPlacementPacket.Face.TOP
    packet.hand = PlayerBlockPlacementPacket.Hand.MAIN
    packet.x = 0.5
    packet.y = 0.5
    packet.z = 0.5
    packet.inside_block = False
    conn.write_packet(packet)

def _parse_xyz(parts, start_index=1):
    if len(parts) < start_index + 3:
        return None
    try:
        x = float(parts[start_index])
        y = float(parts[start_index + 1])
        z = float(parts[start_index + 2])
        return x, y, z
    except Exception:
        return None

def _parse_radius(parts, index=1, default=10, min_radius=1, max_radius=PRUNE_RADIUS):
    radius = default
    if len(parts) > index:
        try:
            radius = int(float(parts[index]))
        except Exception:
            radius = default
    return max(min_radius, min(radius, max_radius))

# --- Enhanced Actions ---
def perform_action(reply, allow_chat=True):
    reply = reply.strip()

    if reply.startswith("!say "):
        message = reply[5:].strip()
        return message if message else None

    if reply in ("!wait", "!noop"):
        return None

    if reply == "!attack":
        swing = AnimationPacket()
        swing.hand = 0
        conn.write_packet(swing)
        return None

    if reply == "!respawn":
        respawn = ClientStatusPacket()
        respawn.action_id = ClientStatusPacket.RESPAWN
        conn.write_packet(respawn)
        return None

    if reply == "!jump":
        jump()
        return None

    if reply == "!circle":
        circle_walk()
        return None

    if reply == "!follow":
        enable_follow()
        return None

    if reply == "!stopfollow":
        disable_follow()
        return None

    if reply.startswith("!wander"):
        parts = reply.split()
        radius = _parse_radius(parts, index=1, default=6, max_radius=24)
        wander(radius=radius)
        return None

    if reply.startswith("!scan"):
        parts = reply.split()
        radius = _parse_radius(parts, index=1, default=DEFAULT_SCAN_RADIUS)
        return describe_scan(radius=radius)

    if reply.startswith("!mine"):
        parts = reply.split()
        coords = _parse_xyz(parts, start_index=1)
        if not coords:
            return "Couldn't mine that, coordinates unclear."
        mine_block(*coords)
        return None

    if reply.startswith("!place"):
        parts = reply.split()
        coords = _parse_xyz(parts, start_index=1)
        if not coords:
            return "Couldn't place that, coordinates unclear."
        place_block(*coords)
        return None

    if reply.startswith("!use") or reply.startswith("!open") or reply.startswith("!craft") or reply.startswith("!chest"):
        parts = reply.split()
        coords = _parse_xyz(parts, start_index=1)
        if not coords:
            return "Couldn't use that, coordinates unclear."
        use_block(*coords)
        return None

    if reply.startswith("!goto"):
        parts = reply.split()
        coords = _parse_xyz(parts, start_index=1)
        if not coords:
            return "Can't get there, lost my map."
        move_to(*coords, sprinting=False)
        return None

    if reply.startswith("!sprint"):
        parts = reply.split()
        coords = _parse_xyz(parts, start_index=1)
        if not coords:
            return "Can't sprint there, too tired."
        move_to(*coords, sprinting=True)
        return None

    if allow_chat:
        return reply
    return None

def send_chat(message):
    if not message:
        return
    chat = ChatPacket()
    chat.message = str(message)[:256]
    conn.write_packet(chat)

def _extract_text(obj):
    if isinstance(obj, str):
        return obj
    if isinstance(obj, dict):
        text = obj.get("text", "")
        extra = obj.get("extra", [])
        if extra:
            text += "".join(_extract_text(item) for item in extra)
        return text
    if isinstance(obj, list):
        return "".join(_extract_text(item) for item in obj)
    return str(obj)

def parse_chat_message(raw):
    try:
        data = json.loads(raw)
    except Exception:
        text = str(raw).strip()
        if text.startswith("<") and ">" in text:
            sender = text[1:text.index(">")].strip()
            message = text[text.index(">") + 1:].strip()
            return sender if sender else None, message
        return None, text

    if isinstance(data, dict) and "translate" in data and "with" in data:
        if isinstance(data.get("with"), list) and len(data["with"]) >= 2:
            sender = _extract_text(data["with"][0]).strip()
            text = _extract_text(data["with"][1]).strip()
            if sender or text:
                return sender if sender else None, text

    text = _extract_text(data).strip()
    if text.startswith("<") and ">" in text:
        sender = text[1:text.index(">")].strip()
        message = text[text.index(">") + 1:].strip()
        return sender if sender else None, message
    return None, text

def enable_follow():
    global follow_mode, follow_target_uuid
    follow_mode = True
    follow_target_uuid = uuid_by_name.get(OWNER)

def disable_follow():
    global follow_mode, follow_target_uuid
    follow_mode = False
    follow_target_uuid = None

def get_entity_position_by_uuid(uuid_value):
    entity_id = entity_id_by_uuid.get(uuid_value)
    if entity_id is None:
        return None
    entity = entity_by_id.get(entity_id)
    if not entity:
        return None
    return entity.get("x"), entity.get("y"), entity.get("z")

def follow_tick():
    global _last_follow_tick
    if not logged_in or not follow_mode:
        return
    now = time.time()
    if now - _last_follow_tick < FOLLOW_TICK_SECONDS:
        return
    _last_follow_tick = now
    target_uuid = follow_target_uuid or uuid_by_name.get(OWNER)
    if not target_uuid:
        return
    target_pos = get_entity_position_by_uuid(target_uuid)
    if not target_pos:
        return
    tx, ty, tz = target_pos
    dist = math.sqrt((tx - current_pos["x"]) ** 2 + (ty - current_pos["y"]) ** 2 + (tz - current_pos["z"]) ** 2)
    if dist > FOLLOW_DISTANCE:
        move_to(tx, ty, tz, sprinting=dist > 8)

def autonomy_tick():
    global _last_autonomy_tick
    if not logged_in or follow_mode:
        return
    if not AUTO_MODE and not current_task:
        return
    now = time.time()
    if now - _last_autonomy_tick < AUTO_TICK_SECONDS:
        return
    _last_autonomy_tick = now
    mode = "task" if current_task else "auto"
    message = "Autonomy tick."
    reply = ask_ai(message, autonomy_history, mode=mode)
    autonomy_history.append({"role": "user", "content": message})
    autonomy_history.append({"role": "assistant", "content": reply})
    _trim_history(autonomy_history, limit=12)
    action_result = perform_action(reply, allow_chat=False)
    if action_result and AUTO_CHAT_ENABLED:
        send_chat(action_result)

def handle_owner_command(sender, text):
    global AUTO_MODE, current_task, _last_autonomy_tick
    if TASK_OWNER_ONLY and sender != OWNER:
        return False

    stripped = text.strip()
    lowered = stripped.lower()
    if lowered.startswith("!task"):
        parts = stripped.split(" ", 1)
        if len(parts) == 1 or not parts[1].strip():
            send_chat("Usage: !task <goal> or !task clear")
            return True
        task_text = parts[1].strip()
        if task_text.lower() in ("clear", "off", "stop"):
            current_task = None
            send_chat("Task cleared.")
            return True
        current_task = task_text
        disable_follow()
        _last_autonomy_tick = 0.0
        send_chat(f"Task set: {current_task}")
        return True

    if lowered.startswith("!auto"):
        parts = lowered.split()
        if len(parts) >= 2 and parts[1] in ("on", "off"):
            AUTO_MODE = parts[1] == "on"
            if AUTO_MODE:
                _last_autonomy_tick = 0.0
            send_chat(f"Auto mode: {'on' if AUTO_MODE else 'off'}")
            return True
        send_chat("Usage: !auto on|off")
        return True

    if lowered.startswith("!scan"):
        parts = lowered.split()
        radius = _parse_radius(parts, index=1, default=DEFAULT_SCAN_RADIUS)
        send_chat(describe_scan(radius))
        return True

    if lowered == "!follow":
        enable_follow()
        send_chat("Following.")
        return True

    if lowered == "!stopfollow":
        disable_follow()
        send_chat("Stopped following.")
        return True

    if lowered == "!where":
        pos = f"({int(current_pos['x'])}, {int(current_pos['y'])}, {int(current_pos['z'])})"
        send_chat(f"My position: {pos}")
        return True

    return False

# --- Chat Handler ---
def handle_chat(packet):
    global MOOD
    msg = packet.json_data
    print("[CHAT]", msg)

    msg_str = str(msg)
    if USERNAME.lower() in msg_str.lower() and "death" in msg_str.lower():
        print("AI_Friend died ?? - Respawning...")
        time.sleep(1)
        respawn = ClientStatusPacket()
        respawn.action_id = ClientStatusPacket.RESPAWN
        conn.write_packet(respawn)
        return

    sender, text = parse_chat_message(msg_str)
    if not text:
        return

    if hasattr(packet, "position") and packet.position != ChatMessagePacket.Position.CHAT:
        return

    if sender and sender == USERNAME:
        return

    if sender and handle_owner_command(sender, text):
        return

    if "kill" in text.lower():
        MOOD = "protective"

    message_for_ai = f"{sender}: {text}" if sender else text
    reply = ask_ai(message_for_ai, conversation, mode="chat")
    conversation.append({"role": "user", "content": message_for_ai})
    action_result = perform_action(reply, allow_chat=True)

    if action_result:
        send_chat(action_result)
        conversation.append({"role": "assistant", "content": action_result})
    else:
        conversation.append({"role": "assistant", "content": reply})
    _trim_history(conversation, limit=12)

# --- Position Updates ---
def handle_position(packet):
    """Track bot's position from server updates"""
    if hasattr(packet, "flags"):
        if packet.flags & packet.FLAG_REL_X:
            current_pos["x"] += packet.x
        else:
            current_pos["x"] = packet.x
        if packet.flags & packet.FLAG_REL_Y:
            current_pos["y"] += packet.y
        else:
            current_pos["y"] = packet.y
        if packet.flags & packet.FLAG_REL_Z:
            current_pos["z"] += packet.z
        else:
            current_pos["z"] = packet.z
        if packet.flags & packet.FLAG_REL_YAW:
            current_pos["yaw"] += packet.yaw
        else:
            current_pos["yaw"] = packet.yaw
        if packet.flags & packet.FLAG_REL_PITCH:
            current_pos["pitch"] += packet.pitch
        else:
            current_pos["pitch"] = packet.pitch
    else:
        current_pos["x"] = packet.x
        current_pos["y"] = packet.y
        current_pos["z"] = packet.z
        if hasattr(packet, "yaw"):
            current_pos["yaw"] = packet.yaw
        if hasattr(packet, "pitch"):
            current_pos["pitch"] = packet.pitch

    if hasattr(packet, "teleport_id"):
        confirm = TeleportConfirmPacket()
        confirm.teleport_id = packet.teleport_id
        conn.write_packet(confirm)

# --- Block Tracking ---
def handle_block_change(packet):
    """Track individual block changes"""
    if not (hasattr(packet, "location") and hasattr(packet, "block_state_id")):
        return
    try:
        x, y, z = _coerce_xyz(packet.location)
    except Exception:
        return
    _track_block(x, y, z, packet.block_state_id)
    _maybe_prune_world_blocks()

def handle_multi_block_change(packet):
    """Track multiple block changes"""
    if not hasattr(packet, "records"):
        return

    try:
        if hasattr(packet, "chunk_section_pos"):
            chunk_x, section_y, chunk_z = _coerce_xyz(packet.chunk_section_pos)
            base_x = chunk_x * 16
            base_y = section_y * 16
            base_z = chunk_z * 16
            for record in packet.records:
                if not hasattr(record, "block_state_id"):
                    continue
                x = base_x + int(getattr(record, "x"))
                y = base_y + int(getattr(record, "y"))
                z = base_z + int(getattr(record, "z"))
                _track_block(x, y, z, getattr(record, "block_state_id"))
        else:
            chunk_x = int(getattr(packet, "chunk_x"))
            chunk_z = int(getattr(packet, "chunk_z"))
            base_x = chunk_x * 16
            base_z = chunk_z * 16
            for record in packet.records:
                if not hasattr(record, "block_state_id"):
                    continue
                x = base_x + int(getattr(record, "x"))
                y = int(getattr(record, "y"))
                z = base_z + int(getattr(record, "z"))
                _track_block(x, y, z, getattr(record, "block_state_id"))
    except Exception:
        return

    _maybe_prune_world_blocks()

# --- Chunk Data Tracking ---
def handle_chunk_data(packet):
    try:
        parse_chunk_sections(packet.chunk_x, packet.chunk_z, packet.bitmask, packet.chunk_data)
    except Exception:
        return
    _maybe_prune_world_blocks()

# --- Entity Tracking ---
def handle_player_list(packet):
    global follow_target_uuid
    for action in packet.actions:
        action_id = getattr(action, "action_id", None)
        if action_id == 0 and hasattr(action, "name"):
            players_by_uuid[action.uuid] = {
                "name": action.name,
                "display_name": getattr(action, "display_name", None)
            }
            uuid_by_name[action.name] = action.uuid
            if action.name == OWNER and follow_mode:
                follow_target_uuid = action.uuid
        elif action_id == 4:
            player = players_by_uuid.pop(action.uuid, None)
            if player:
                name = player.get("name")
                if name and uuid_by_name.get(name) == action.uuid:
                    uuid_by_name.pop(name, None)

def handle_spawn_player(packet):
    entity_by_id[packet.entity_id] = {
        "uuid": packet.player_UUID,
        "x": packet.x,
        "y": packet.y,
        "z": packet.z,
        "yaw": packet.yaw,
        "pitch": packet.pitch,
        "last_seen": time.time()
    }
    entity_id_by_uuid[packet.player_UUID] = packet.entity_id

def handle_entity_position_delta(packet):
    entity = entity_by_id.get(packet.entity_id)
    if not entity:
        return
    dx = getattr(packet, "delta_x_float", 0.0)
    dy = getattr(packet, "delta_y_float", 0.0)
    dz = getattr(packet, "delta_z_float", 0.0)
    entity["x"] = entity.get("x", 0.0) + dx
    entity["y"] = entity.get("y", 0.0) + dy
    entity["z"] = entity.get("z", 0.0) + dz
    entity["last_seen"] = time.time()

def handle_entity_look(packet):
    entity = entity_by_id.get(packet.entity_id)
    if not entity:
        return
    entity["yaw"] = packet.yaw
    entity["pitch"] = packet.pitch
    entity["last_seen"] = time.time()

# --- Combat ---
def handle_combat(packet):
    if hasattr(packet, 'event'):
        if packet.event == 2:
            print("AI_Friend died 💀")
            respawn = ClientStatusPacket()
            respawn.action_id = ClientStatusPacket.RESPAWN
            conn.write_packet(respawn)

# --- Login ---
def handle_login(packet):
    global logged_in, _last_autonomy_tick
    print("Logged in.")
    logged_in = True
    _last_autonomy_tick = 0.0
    ensure_block_state_mapping()
    if block_data_load_error:
        print(f"Block data load failed: {block_data_load_error}")
    if register_chunk_packet():
        print(f"Chunk packet registered: 0x{chunk_packet_id:02x}")
    elif chunk_packet_load_error:
        print(f"Chunk packet id load failed: {chunk_packet_load_error}")
    # Auto-respawn if joining dead
    time.sleep(0.5)
    respawn = ClientStatusPacket()
    respawn.action_id = ClientStatusPacket.RESPAWN
    conn.write_packet(respawn)
    time.sleep(0.5)
    
    pos = PositionAndLookPacket()
    pos.x = 0
    pos.feet_y = 100
    pos.z = 0
    pos.yaw = 0
    pos.pitch = 0
    pos.on_ground = True
    conn.write_packet(pos)
    time.sleep(1)
    tp = ChatPacket()
    tp.message = f"/tp {USERNAME} {OWNER}"
    conn.write_packet(tp)

# --- Register ---
conn.register_packet_listener(handle_chat, ChatMessagePacket)
conn.register_packet_listener(handle_combat, CombatEventPacket)
conn.register_packet_listener(handle_login, LoginSuccessPacket)
conn.register_packet_listener(handle_position, PlayerPositionAndLookPacket)
conn.register_packet_listener(handle_block_change, BlockChangePacket)
conn.register_packet_listener(handle_multi_block_change, MultiBlockChangePacket)
conn.register_packet_listener(handle_chunk_data, ChunkDataPacket)
conn.register_packet_listener(handle_player_list, PlayerListItemPacket)
conn.register_packet_listener(handle_spawn_player, SpawnPlayerPacket)
conn.register_packet_listener(handle_entity_position_delta, EntityPositionDeltaPacket)
conn.register_packet_listener(handle_entity_look, EntityLookPacket)

# --- Run ---
def start():
    print(f"Connecting as {USERNAME}...")
    conn.connect()
    while True:
        follow_tick()
        autonomy_tick()
        time.sleep(0.1)

if __name__ == "__main__":
    start()
