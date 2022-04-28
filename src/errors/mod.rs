#[derive(Debug)]
pub enum PhysEngineErrors {
    InvalidInputSize,
    NotCoplanar,
    PolygonInvalidVertexCount,
    IndicesOutOfBounds,
}
