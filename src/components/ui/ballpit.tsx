import React, { useRef, useEffect, useMemo } from "react";
import {
  Clock, PerspectiveCamera, Scene, WebGLRenderer, SRGBColorSpace, MathUtils,
  Vector2, Vector3, MeshPhysicalMaterial, Color, Object3D, InstancedMesh,
  PMREMGenerator, SphereGeometry, AmbientLight, PointLight, ACESFilmicToneMapping,
  Raycaster, Plane, Mesh, CanvasTexture, RepeatWrapping,
} from "three";
import { RoomEnvironment } from "three/examples/jsm/environments/RoomEnvironment.js";
import { cn } from "@/lib/utils";

class ThreeRoot {
  private cfg: any;
  private resizeObserver?: ResizeObserver;
  private intersectionObserver?: IntersectionObserver;
  private resizeTimer?: number;
  private rafId = 0;
  private clock = new Clock();
  private state = { elapsed: 0, delta: 0 };
  private isVisible = false;
  private isAnimating = false;
  canvas: HTMLCanvasElement;
  camera: PerspectiveCamera;
  scene: Scene;
  renderer: WebGLRenderer;
  size: any = { width: 0, height: 0, wWidth: 0, wHeight: 0, ratio: 0 };
  onBeforeRender: (s: { elapsed: number; delta: number }) => void = () => {};
  onAfterResize: (s: any) => void = () => {};

  constructor(cfg: any) {
    this.cfg = cfg;
    this.canvas = cfg.canvas;
    this.camera = new PerspectiveCamera(50, 1, 0.1, 100);
    this.scene = new Scene();
    this.renderer = new WebGLRenderer({
      canvas: this.canvas,
      powerPreference: "high-performance",
      alpha: true,
      antialias: true,
    });
    this.renderer.outputColorSpace = SRGBColorSpace;
    this.canvas.style.display = "block";
    this.initObservers();
    this.resize();
  }
  private initObservers() {
    const parent = this.canvas.parentNode as Element | null;
    if (parent) {
      this.resizeObserver = new ResizeObserver(() => this.deferResize());
      this.resizeObserver.observe(parent);
    } else {
      window.addEventListener("resize", this.deferResize);
    }
    this.intersectionObserver = new IntersectionObserver(
      (entries) => {
        this.isAnimating = entries[0].isIntersecting;
        this.isAnimating ? this.start() : this.stop();
      },
      { threshold: 0 }
    );
    this.intersectionObserver.observe(this.canvas);
    document.addEventListener("visibilitychange", this.onVisibility);
  }
  private deferResize = () => {
    if (this.resizeTimer) clearTimeout(this.resizeTimer);
    this.resizeTimer = window.setTimeout(() => this.resize(), 100);
  };
  private onVisibility = () => {
    if (this.isAnimating) (document.hidden ? this.stop() : this.start());
  };
  resize() {
    const parent = this.canvas.parentNode as HTMLElement | null;
    const w = parent ? parent.offsetWidth : window.innerWidth;
    const h = parent ? parent.offsetHeight : window.innerHeight;
    this.size.width = w; this.size.height = h; this.size.ratio = w / h;
    this.camera.aspect = this.size.ratio;
    this.camera.updateProjectionMatrix();
    const fovRad = (this.camera.fov * Math.PI) / 180;
    this.size.wHeight = 2 * Math.tan(fovRad / 2) * this.camera.position.z;
    this.size.wWidth = this.size.wHeight * this.camera.aspect;
    this.renderer.setSize(w, h);
    const isMobile = window.innerWidth < 768;
    this.renderer.setPixelRatio(Math.min(window.devicePixelRatio, isMobile ? 1 : 2));
    this.onAfterResize(this.size);
  }
  private start = () => {
    if (this.isVisible) return;
    this.isVisible = true;
    this.clock.start();
    const tick = () => {
      this.rafId = requestAnimationFrame(tick);
      this.state.delta = this.clock.getDelta();
      this.state.elapsed += this.state.delta;
      this.onBeforeRender(this.state);
      this.renderer.render(this.scene, this.camera);
    };
    tick();
  };
  private stop = () => {
    if (!this.isVisible) return;
    cancelAnimationFrame(this.rafId);
    this.isVisible = false;
    this.clock.stop();
  };
  dispose() {
    this.stop();
    this.resizeObserver?.disconnect();
    this.intersectionObserver?.disconnect();
    window.removeEventListener("resize", this.deferResize);
    document.removeEventListener("visibilitychange", this.onVisibility);
    this.scene.clear();
    this.renderer.dispose();
  }
}

class Physics {
  config: any;
  positionData: Float32Array;
  velocityData: Float32Array;
  sizeData: Float32Array;
  center = new Vector3();
  constructor(config: any) {
    this.config = config;
    this.positionData = new Float32Array(3 * config.count);
    this.velocityData = new Float32Array(3 * config.count);
    this.sizeData = new Float32Array(config.count);
    this.initPositions();
    this.setSizes();
  }
  private initPositions() {
    const { count, maxX, maxY, maxZ } = this.config;
    this.center.toArray(this.positionData, 0);
    for (let i = 1; i < count; i++) {
      const idx = 3 * i;
      this.positionData[idx] = MathUtils.randFloatSpread(2 * maxX);
      this.positionData[idx + 1] = MathUtils.randFloatSpread(2 * maxY);
      this.positionData[idx + 2] = MathUtils.randFloatSpread(2 * maxZ);
    }
  }
  setSizes() {
    const { count, size0, minSize, maxSize } = this.config;
    this.sizeData[0] = size0;
    for (let i = 1; i < count; i++) this.sizeData[i] = MathUtils.randFloat(minSize, maxSize);
  }
  update(deltaInfo: { delta: number }) {
    const { config, center, positionData, sizeData, velocityData } = this;
    const startIdx = config.controlSphere0 ? 1 : 0;
    if (config.controlSphere0) {
      new Vector3().fromArray(positionData, 0).lerp(center, 0.1).toArray(positionData, 0);
      new Vector3(0, 0, 0).toArray(velocityData, 0);
    }
    for (let i = startIdx; i < config.count; i++) {
      const base = 3 * i;
      const pos = new Vector3().fromArray(positionData, base);
      const vel = new Vector3().fromArray(velocityData, base);
      vel.y -= deltaInfo.delta * config.gravity * sizeData[i];
      vel.multiplyScalar(config.friction);
      vel.clampLength(0, config.maxVelocity);
      pos.add(vel);
      for (let j = i + 1; j < config.count; j++) {
        const otherBase = 3 * j;
        const otherPos = new Vector3().fromArray(positionData, otherBase);
        const diff = new Vector3().subVectors(otherPos, pos);
        const dist = diff.length();
        const sumRadius = sizeData[i] + sizeData[j];
        if (dist < sumRadius) {
          const overlap = (sumRadius - dist) * 0.5;
          diff.normalize();
          pos.addScaledVector(diff, -overlap);
          otherPos.addScaledVector(diff, overlap);
          pos.toArray(positionData, base);
          otherPos.toArray(positionData, otherBase);
        }
      }
      if (Math.abs(pos.x) + sizeData[i] > config.maxX) { pos.x = Math.sign(pos.x) * (config.maxX - sizeData[i]); vel.x *= -config.wallBounce; }
      if (pos.y - sizeData[i] < -config.maxY) { pos.y = -config.maxY + sizeData[i]; vel.y *= -config.wallBounce; }
      if (Math.abs(pos.z) + sizeData[i] > config.maxZ) { pos.z = Math.sign(pos.z) * (config.maxZ - sizeData[i]); vel.z *= -config.wallBounce; }
      pos.toArray(positionData, base);
      vel.toArray(velocityData, base);
    }
  }
}

function makeLabelTexture(text: string, bgColor: string) {
  const size = 1024;
  const canvas = document.createElement("canvas");
  canvas.width = size; canvas.height = size;
  const ctx = canvas.getContext("2d")!;
  // Flat bright base — no overlay covering the text
  ctx.fillStyle = lighten(bgColor, 0.12);
  ctx.fillRect(0, 0, size, size);
  // Label
  ctx.textAlign = "center";
  ctx.textBaseline = "middle";
  const words = text.split(" ");
  const lines: string[] = [];
  let line = "";
  ctx.font = "800 56px system-ui, -apple-system, Segoe UI, sans-serif";
  for (const w of words) {
    const test = line ? line + " " + w : w;
    if (ctx.measureText(test).width > size * 0.36 && line) {
      lines.push(line); line = w;
    } else line = test;
  }
  if (line) lines.push(line);
  let fontSize = lines.length <= 1 ? 64 : lines.length === 2 ? 50 : 40;
  ctx.font = `800 ${fontSize}px system-ui, -apple-system, Segoe UI, sans-serif`;
  ctx.imageSmoothingEnabled = true;
  ctx.imageSmoothingQuality = "high";
  const lineHeight = fontSize * 1.1;
  const totalHeight = lines.length * lineHeight;
  const drawAt = (cx: number) => {
    const startY = size / 2 - totalHeight / 2 + lineHeight / 2;
    // crisp dark outline (no blur — cleaner edges)
    ctx.lineWidth = 5;
    ctx.lineJoin = "round";
    ctx.miterLimit = 2;
    ctx.strokeStyle = "rgba(15,23,42,.85)";
    lines.forEach((l, i) => ctx.strokeText(l, cx, startY + i * lineHeight));
    ctx.fillStyle = "#FFFFFF";
    lines.forEach((l, i) => ctx.fillText(l, cx, startY + i * lineHeight));
  };
  drawAt(size * 0.25);
  drawAt(size * 0.75);
  const tex = new CanvasTexture(canvas);
  tex.wrapS = RepeatWrapping;
  tex.wrapT = RepeatWrapping;
  tex.anisotropy = 16;
  tex.needsUpdate = true;
  return tex;
}

function shiftHex(hex: string, amt: number) {
  const m = hex.replace("#", "");
  const n = parseInt(m.length === 3 ? m.split("").map(c => c + c).join("") : m, 16);
  let r = (n >> 16) & 0xff, g = (n >> 8) & 0xff, b = n & 0xff;
  r = Math.max(0, Math.min(255, Math.round(r + 255 * amt)));
  g = Math.max(0, Math.min(255, Math.round(g + 255 * amt)));
  b = Math.max(0, Math.min(255, Math.round(b + 255 * amt)));
  return `rgb(${r},${g},${b})`;
}
function lighten(hex: string, amt: number) { return shiftHex(hex, amt); }
function darken(hex: string, amt: number) { return shiftHex(hex, -amt); }

class LabeledSpheres extends Object3D {
  config: any;
  physics: Physics;
  meshes: Mesh[] = [];
  ambientLight: AmbientLight;
  light: PointLight;
  envTexture: any;
  textures: CanvasTexture[] = [];
  spinSpeeds: number[] = [];
  spinBoost = 0;
  constructor(renderer: WebGLRenderer, params: any) {
    super();
    const pmrem = new PMREMGenerator(renderer);
    this.envTexture = pmrem.fromScene(new RoomEnvironment(renderer)).texture;
    pmrem.dispose();
    this.config = params;
    this.physics = new Physics(params);
    const geometry = new SphereGeometry(1, 48, 48);
    const labels: string[] = params.labels || [];
    const colors = (params.colors || []).map((c: any) => (c instanceof Color ? c : new Color(c)));
    for (let i = 0; i < params.count; i++) {
      const label = labels[i % labels.length] || "";
      const color = colors[i % colors.length] || new Color("#3B82F6");
      const tex = makeLabelTexture(label, "#" + color.getHexString());
      this.textures.push(tex);
      const material = new MeshPhysicalMaterial({
        envMap: this.envTexture,
        map: tex,
        emissive: color.clone(),
        emissiveIntensity: 0.7,
        ...params.materialParams,
        metalness: 0.0,
        roughness: 0.45,
        clearcoat: 0.3,
        clearcoatRoughness: 0.4,
        envMapIntensity: 0.6,
      });
      const mesh = new Mesh(geometry, material);
      // initial random rotation so labels start at varied angles
      mesh.rotation.y = Math.random() * Math.PI * 2;
      mesh.rotation.x = (Math.random() - 0.5) * 0.4;
      this.meshes.push(mesh);
      this.spinSpeeds.push(MathUtils.randFloat(0.15, 0.45) * (Math.random() < 0.5 ? -1 : 1));
      this.add(mesh);
    }
    this.ambientLight = new AmbientLight(0xffffff, params.ambientIntensity);
    this.add(this.ambientLight);
    this.light = new PointLight(0xffffff, params.lightIntensity, 100, 1);
    this.add(this.light);
  }
  update(deltaInfo: { delta: number }) {
    this.physics.update(deltaInfo);
    // decay cursor-driven spin boost
    this.spinBoost = Math.max(0, this.spinBoost - deltaInfo.delta * 1.4);
    const boost = 1 + this.spinBoost * 6;
    for (let i = 0; i < this.meshes.length; i++) {
      const m = this.meshes[i];
      m.position.fromArray(this.physics.positionData, 3 * i);
      m.scale.setScalar(this.physics.sizeData[i]);
      m.rotation.y += this.spinSpeeds[i] * deltaInfo.delta * boost;
    }
    if (this.config.controlSphere0) this.light.position.fromArray(this.physics.positionData, 0);
  }
}

const tmpObj = new Object3D();
class Spheres extends InstancedMesh {
  config: any;
  physics: Physics;
  ambientLight: AmbientLight;
  light: PointLight;
  constructor(renderer: WebGLRenderer, params: any) {
    const pmrem = new PMREMGenerator(renderer);
    const envTexture = pmrem.fromScene(new RoomEnvironment(renderer)).texture;
    pmrem.dispose();
    const geometry = new SphereGeometry(1, 24, 24);
    const material = new MeshPhysicalMaterial({ envMap: envTexture, ...params.materialParams });
    super(geometry, material, params.count);
    this.config = params;
    this.physics = new Physics(this.config);
    this.ambientLight = new AmbientLight(0xffffff, params.ambientIntensity);
    this.add(this.ambientLight);
    this.light = new PointLight(0xffffff, params.lightIntensity, 100, 1);
    this.add(this.light);
    this.setColors(this.config.colors);
  }
  setColors(colors: (string | Color)[]) {
    if (!Array.isArray(colors) || !colors.length) return;
    const cs = colors.map((c) => (c instanceof Color ? c : new Color(c)));
    for (let i = 0; i < this.count; i++) this.setColorAt(i, cs[i % cs.length]);
    if (this.instanceColor) this.instanceColor.needsUpdate = true;
  }
  update(deltaInfo: { delta: number }) {
    this.physics.update(deltaInfo);
    for (let i = 0; i < this.count; i++) {
      tmpObj.position.fromArray(this.physics.positionData, 3 * i);
      tmpObj.scale.setScalar(this.physics.sizeData[i]);
      tmpObj.updateMatrix();
      this.setMatrixAt(i, tmpObj.matrix);
    }
    this.instanceMatrix.needsUpdate = true;
    if (this.config.controlSphere0) this.light.position.fromArray(this.physics.positionData, 0);
  }
}

const pointer = new Vector2();
const pointerPrev = new Vector2();
let pointerVel = 0;
function onPointerMove(e: PointerEvent) {
  const nx = (e.clientX / window.innerWidth) * 2 - 1;
  const ny = -(e.clientY / window.innerHeight) * 2 + 1;
  const dx = nx - pointerPrev.x;
  const dy = ny - pointerPrev.y;
  pointerVel = Math.min(1, pointerVel + Math.sqrt(dx * dx + dy * dy) * 6);
  pointerPrev.set(nx, ny);
  pointer.set(nx, ny);
}

const defaultBallpitConfig = {
  count: 200,
  materialParams: { metalness: 0.7, roughness: 0.3, clearcoat: 1, clearcoatRoughness: 0.2 },
  minSize: 0.3, maxSize: 0.8, size0: 1.0,
  gravity: 0.4, friction: 0.995, wallBounce: 0.2, maxVelocity: 0.1,
  maxX: 10, maxY: 10, maxZ: 10,
  controlSphere0: true, followCursor: true,
  lightIntensity: 3, ambientIntensity: 1.5,
};

type BallpitProps = Partial<typeof defaultBallpitConfig> & {
  colors?: (string | Color)[];
  labels?: string[];
  className?: string;
};

const defaultColors = ["#1E40AF", "#3B82F6", "#60A5FA", "#93C5FD", "#DBEAFE"];

export const Ballpit: React.FC<BallpitProps> = ({ className, colors, labels, ...rest }) => {
  const canvasRef = useRef<HTMLCanvasElement>(null);
  const config = useMemo(
    () => ({ ...defaultBallpitConfig, ...rest, colors: colors ?? defaultColors, labels }),
    [rest, colors, labels]
  );

  useEffect(() => {
    const canvas = canvasRef.current;
    if (!canvas) return;

    const three = new ThreeRoot({ canvas });
    three.renderer.toneMapping = ACESFilmicToneMapping;
    three.camera.position.set(0, 0, 20);

    const useLabels = Array.isArray(config.labels) && config.labels.length > 0;
    const spheres: any = useLabels
      ? new LabeledSpheres(three.renderer, config)
      : new Spheres(three.renderer, config);
    three.scene.add(spheres);

    const raycaster = new Raycaster();
    const plane = new Plane(new Vector3(0, 0, 1), 0);
    const intersectionPoint = new Vector3();

    if (config.followCursor) window.addEventListener("pointermove", onPointerMove);

    three.onBeforeRender = (deltaInfo) => {
      // pump cursor velocity into label spin
      if (useLabels) {
        spheres.spinBoost = Math.min(1.2, spheres.spinBoost + pointerVel * 0.6);
      }
      pointerVel = Math.max(0, pointerVel - deltaInfo.delta * 2.5);
      if (config.followCursor) {
        raycaster.setFromCamera(pointer, three.camera);
        if (raycaster.ray.intersectPlane(plane, intersectionPoint)) {
          spheres.physics.center.copy(intersectionPoint);
        }
      }
      spheres.update(deltaInfo);
    };

    three.onAfterResize = (size) => {
      spheres.physics.config.maxX = size.wWidth / 2;
      spheres.physics.config.maxY = size.wHeight / 2;
      spheres.physics.config.maxZ = size.wWidth / 4;
    };

    return () => {
      if (config.followCursor) window.removeEventListener("pointermove", onPointerMove);
      three.dispose();
    };
  }, [config]);

  return <canvas ref={canvasRef} className={cn("absolute inset-0 w-full h-full", className)} />;
};

export default Ballpit;
