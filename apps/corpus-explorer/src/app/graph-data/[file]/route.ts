import { getGraphBuckets } from "@/lib/graph-bucket-data";

/** Static JSON files of the bucketed /graph data (#491): one per bucket, plus lookup and search. */
export const dynamic = "force-static";
export const dynamicParams = false;

export function generateStaticParams() {
  const { buckets } = getGraphBuckets();
  return [...buckets.map((bucket) => ({ file: `${bucket.id}.json` })), { file: "lookup.json" }, { file: "search.json" }];
}

export async function GET(_request: Request, { params }: { params: Promise<{ file: string }> }) {
  const { file } = await params;
  const data = getGraphBuckets();
  if (file === "lookup.json") return Response.json(data.lookup);
  if (file === "search.json") return Response.json(data.search);
  const bucket = data.buckets.find((entry) => `${entry.id}.json` === file);
  return bucket ? Response.json(bucket) : new Response("Not found", { status: 404 });
}
