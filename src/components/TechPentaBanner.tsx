import { Gravity, MatterBody } from "@/components/ui/gravity"

const TECHS = [
  { label: "react", bg: "#0015ff", x: "20%", y: "10%" },
  { label: "typescript", bg: "#3178c6", x: "35%", y: "20%" },
  { label: "node.js", bg: "#1f464d", x: "50%", y: "8%", angle: 8 },
  { label: "tailwind", bg: "#06b6d4", x: "65%", y: "18%" },
  { label: "vite", bg: "#ffd726", x: "78%", y: "10%", color: "#08060d" },
  { label: "matter-js", bg: "#ff5941", x: "30%", y: "32%", angle: -6 },
  { label: "framer", bg: "#E794DA", x: "55%", y: "30%" },
  { label: "next.js", bg: "#08060d", x: "72%", y: "32%" },
]

export function TechPentaBanner() {
  return (
    <div
      className="relative min-h-[560px] overflow-hidden bg-gradient-to-b from-white via-[#faf7ff] to-[#efe6ff]"
      style={{ width: '100vw', marginLeft: 'calc(50% - 50vw)' }}
    >
      <div className="pointer-events-none absolute inset-0 flex items-center justify-center">
        <h1 className="text-[22vw] font-black tracking-tighter text-[#aa3bff]/10 select-none leading-none whitespace-nowrap">
          techpenta
        </h1>
      </div>

      <div className="relative z-10 pt-16 px-6 text-center">
        <p className="text-sm uppercase tracking-[0.3em] text-[#6b6375]">
          welcome to
        </p>
        <h2 className="mt-3 text-5xl sm:text-6xl md:text-7xl font-bold text-[#08060d]">
          TechPenta
        </h2>
        <p className="mt-4 text-base sm:text-lg text-[#6b6375] max-w-xl mx-auto">
          building modern products with the technologies below — drag them around.
        </p>
      </div>

      <Gravity gravity={{ x: 0, y: 1 }} className="w-full h-full">
        {TECHS.map((t) => (
          <MatterBody
            key={t.label}
            matterBodyOptions={{ friction: 0.5, restitution: 0.3 }}
            x={t.x}
            y={t.y}
            angle={t.angle}
          >
            <div
              className="text-lg sm:text-xl md:text-2xl font-medium rounded-full hover:cursor-grab px-7 py-3 shadow-lg"
              style={{ backgroundColor: t.bg, color: t.color ?? "#ffffff" }}
            >
              {t.label}
            </div>
          </MatterBody>
        ))}
      </Gravity>
    </div>
  )
}

export default TechPentaBanner
