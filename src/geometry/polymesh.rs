//! This module contains an implementation of a [`PolyMesh`] representing a mesh
//! of polygons. The mesh uses the Face-Vertex data structure to store its data.
//! The [`PolyMesh`] stores the associated vertex data for each face in a [`Vec`].
//!
//! The [`PolyMesh`] is a more general version of the [`TriMesh`] and can be used
//! to represent any mesh with any number of vertices per face.
//!
//! [`PolyMesh`] types can be converted to [`TriMesh`] types by using the [`PolyMesh::into_tri_mesh`]
//! method. This method will construct a new [`TriMesh`] with the same vertex data as
//! the [`PolyMesh`] while triangulating the faces of the [`PolyMesh`] with more than
//! 3 vertices. This method will aim to avoid creating slivers in the resulting
//! mesh.
//!
//! [`TriMesh`] types can be converted to [`PolyMesh`] types by using the [`TriMesh::into_poly_mesh`]
//! method. This method will construct a new [`PolyMesh`] with the same vertex data as
//! the [`TriMesh`] while converting the triangles of the [`TriMesh`] into faces with
//! 3 vertices.
//!
//! TODO: Add more rigorous tests for [`PolyMesh`] methods.
//! FIXME: Ensure documentation is correct.

use super::primitives::Polygon;
use super::trimesh::TriMesh;
use super::utils::{get_normal, is_coplanar};
use crate::errors::PhysEngineErrors;

use ultraviolet::Vec3;

/// A struct representing a mesh of polygons. Contains
/// a [`Vec<Polygon>`] of the polygons in the mesh. The [`PolyMesh`] also contains
/// a [`Vec<Vec3>`] of the vertices in the mesh. The polygons contain indices
/// into the [`Vec<Vec3>`] of the vertices.
///
/// The polygons must follow the following rules:
/// * The vertices must be coplanar.
/// * There must be at least 3 vertices.
///
/// It is recommended that the polygons are convex. This is not enforced. If
/// polygon is convex, the normal will be calculated from the vertices by
/// assuming the vertices are in counter-clockwise order and applying the
/// right-hand rule. If not convex, the normal will be guessed from the first
/// three vertices. These normals can be incorrect, but flippable using the
/// [`PolyMesh::flip_normal`] method.
#[derive(Debug, Clone, Default)]
pub struct PolyMesh {
    /// The list of polygons in the mesh.
    pub(crate) polygons: Vec<Polygon>,
    /// The list of vertices in the mesh.
    pub(crate) vertices: Vec<Vec3>,
}

impl From<TriMesh> for PolyMesh {
    /// Converts a [`TriMesh`] into a [`PolyMesh`]. This method will convert the
    /// triangles of the [`TriMesh`] into polygons with 3 vertices.
    ///
    /// See [`TriMesh::into_poly_mesh`] for more information.
    fn from(mesh: TriMesh) -> Self {
        mesh.into_poly_mesh()
    }
}

impl PolyMesh {
    /// Creates empty [`PolyMesh`] with no vertices or polygons.
    ///
    /// # Returns
    /// An empty [`PolyMesh`].
    ///
    /// # Examples
    /// ```
    /// use phys_engine::geometry::polymesh::PolyMesh;
    /// use ultraviolet::Vec3;
    ///
    /// let mesh = PolyMesh::new();
    ///
    /// assert_eq!(mesh.vertices().len(), 0);
    /// assert_eq!(mesh.polygons().len(), 0);
    /// ```
    pub fn new() -> Self {
        Self::default()
    }

    /// Creates a [`PolyMesh`] from a list of vertices and a list of polygons.
    ///
    /// # Arguments
    /// * `vertices` - A list of vertices.
    /// * `polygons` - A list of polygons.
    ///
    /// # Returns
    /// An [`Result<PolyMesh, PhysEngineErrors>`] containing [`Ok(PolyMesh)`] if the vertices and
    /// polygons are valid, [`Err(PhysEngineErrors)`] otherwise. The vertices and polygons are
    /// valid if:
    /// * Polygons do not contain any vertex that is not in the
    /// vertices list. Otherwise, a [`PhysEngineErrors::IndicesOutOfBounds`] error is returned.
    /// * Polygons are coplanar. Otherwise, a [`PhysEngineErrors::NotCoplanar`] error is returned.
    ///
    /// # Examples
    /// ```
    /// use phys_engine::geometry::polymesh::PolyMesh;
    /// use phys_engine::geometry::primitives::Polygon;
    /// use ultraviolet::Vec3;
    ///
    /// let vertices = [
    ///    Vec3::new(0.0, 0.0, 0.0),
    ///    Vec3::new(1.0, 0.0, 0.0),
    ///    Vec3::new(1.0, 1.0, 0.0),
    ///    Vec3::new(0.0, 1.0, 0.0)
    /// ];
    /// let polygons = vec![
    ///   Polygon::new(&[0, 1, 2, 3], &vertices).unwrap()
    /// ];
    ///
    /// let mesh = PolyMesh::from(&vertices, &polygons).unwrap();
    ///
    /// assert_eq!(mesh.vertices().len(), 4);
    /// assert_eq!(mesh.polygons().len(), 1);
    /// assert_eq!(mesh.polygons()[0].vertices(), vec![0, 1, 2, 3]);
    /// ```
    pub fn from(vertices: &[Vec3], polygons: &[Polygon]) -> Result<Self, PhysEngineErrors> {
        if polygons
            .iter()
            .flat_map(|f| &f.vertices)
            .any(|&f| f >= vertices.len())
        {
            return Err(PhysEngineErrors::IndicesOutOfBounds);
        }
        for polygon in polygons {
            if !is_coplanar(
                &polygon
                    .vertices
                    .iter()
                    .map(|&f| vertices[f])
                    .collect::<Vec<_>>(),
            ) {
                return Err(PhysEngineErrors::NotCoplanar);
            }
            if polygon.vertices.len() < 3 {
                return Err(PhysEngineErrors::PolygonInvalidVertexCount);
            }
        }
        Ok(Self {
            vertices: vertices.to_vec(),
            polygons: polygons.to_vec(),
        })
    }

    /// Returns a reference to the list of polygons in the [`PolyMesh`].
    ///
    /// # Returns
    /// A reference to the list of polygons in the [`PolyMesh`].
    pub fn polygons(&self) -> &[Polygon] {
        &self.polygons
    }

    /// Returns a reference to the list of vertices in the [`PolyMesh`].
    ///
    /// # Returns
    /// A reference to the list of vertices in the [`PolyMesh`].
    pub fn vertices(&self) -> &[Vec3] {
        &self.vertices
    }

    /// Adds a new polygon to the [`TriMesh`].
    ///
    /// # Arguments
    /// * `vertices` - A slice of vertices that make up the polygon as [`Vec3`]s.
    ///
    /// # Note
    /// This method has the danger of having duplicate vertices in the mesh.
    ///
    /// # Examples
    /// ```
    /// use phys_engine::geometry::polymesh::PolyMesh;
    /// use ultraviolet::Vec3;
    ///
    /// let mut mesh = PolyMesh::new();
    ///
    /// mesh.add_polygon(&vec![
    ///    Vec3::new(0.0, 0.0, 0.0),
    ///    Vec3::new(1.0, 0.0, 0.0),
    ///    Vec3::new(1.0, 1.0, 0.0),
    ///    Vec3::new(0.0, 1.0, 0.0)
    /// ]);
    ///
    /// assert_eq!(mesh.vertices().len(), 4);
    /// assert_eq!(mesh.polygons().len(), 1);
    ///
    /// assert_eq!(mesh.polygons()[0].vertices(), vec![0, 1, 2, 3]);
    /// assert_eq!(mesh.polygons()[0].normal(), Vec3::new(0.0, 0.0, 1.0));
    /// ```
    ///
    pub fn add_polygon(&mut self, vertices: &[Vec3]) -> Result<(), PhysEngineErrors> {
        if vertices.len() < 3 {
            return Err(PhysEngineErrors::PolygonInvalidVertexCount);
        }

        if !is_coplanar(vertices) {
            return Err(PhysEngineErrors::NotCoplanar);
        }

        self.polygons.push(Polygon {
            vertices: (self.vertices.len()..self.vertices.len() + vertices.len()).collect(),
            normal: get_normal(vertices[0], vertices[1], vertices[2]),
        });
        self.vertices.extend(vertices);
        Ok(())
    }

    /// Deduplicate vertices in the [`PolyMesh`]. This method is useful when you have a
    /// [`PolyMesh`] that has duplicate vertices. This method will remove all duplicate vertices
    /// and replace them with a single vertex. For more information, see the
    /// [`TriMesh::dedup_vertices`] method.
    ///
    /// # Notes
    /// Unlike [`TriMesh::dedup_vertices`], this method does not have a `max_dist` parameter.
    /// This is because the vertices in a [`PolyMesh`] are guaranteed to be coplanar, and even
    /// small vertex displacements can cause the polygons to be non-coplanar.
    ///
    /// # Examples
    /// ```
    /// use phys_engine::geometry::polymesh::PolyMesh;
    /// use ultraviolet::Vec3;
    ///
    /// let mut mesh = PolyMesh::new();
    /// mesh.add_polygon(&vec![
    ///   Vec3::new(0.0, 0.0, 0.0),
    ///   Vec3::new(1.0, 0.0, 0.0),
    ///   Vec3::new(1.0, 1.0, 0.0),
    ///   Vec3::new(0.0, 1.0, 0.0)
    /// ]);
    ///
    /// mesh.add_polygon(&vec![
    ///   Vec3::new(0.0, 0.0, 0.0),
    ///   Vec3::new(1.0, 0.0, 0.0),
    ///   Vec3::new(1.0, 1.0, 0.0),
    ///   Vec3::new(0.0, 1.0, 0.0)
    /// ]);
    ///
    /// mesh.dedup_vertices();
    ///
    /// assert_eq!(mesh.vertices().len(), 4);
    /// assert_eq!(mesh.polygons().len(), 2);
    /// assert_eq!(mesh.polygons()[0].vertices(), vec![0, 1, 2, 3]);
    /// assert_eq!(mesh.polygons()[1].vertices(), vec![0, 1, 2, 3]);
    /// ```
    pub fn dedup_vertices(&mut self) {
        let mut new_vertices = Vec::new();
        let mut new_polygons = Vec::new();

        let mut vertex_map = Vec::new();

        self.vertices
            .iter()
            .for_each(|v| match new_vertices.iter().position(|nv| v == nv) {
                Some(i) => vertex_map.push(i),
                None => {
                    new_vertices.push(*v);
                    vertex_map.push(new_vertices.len() - 1);
                }
            });

        self.polygons.iter().for_each(|p| {
            new_polygons.push(Polygon {
                vertices: p.vertices.iter().map(|i| vertex_map[*i]).collect(),
                normal: p.normal,
            });
        });

        self.vertices = new_vertices;
        self.polygons = new_polygons;
    }

    /// Remove unused vertices from the [`PolyMesh`]. This method is in-place.
    /// This method is useful for meshes that have many hanging vertices. This
    /// method removes all vertices that are not referenced by any polygon. For
    /// more information, see the [`TriMesh::remove_unused_vertices`] method.
    ///
    /// # Examples
    /// ```
    /// use phys_engine::geometry::polymesh::PolyMesh;
    /// use phys_engine::geometry::primitives::Polygon;
    /// use ultraviolet::Vec3;
    ///
    /// let vertices = vec![
    ///     Vec3::new(0.0, 0.0, 0.0),
    ///     Vec3::new(1.0, 0.0, 0.0),
    ///     Vec3::new(1.0, 1.0, 0.0),
    ///     Vec3::new(0.0, 0.0, 1.0),
    ///     Vec3::new(0.0, 1.0, 0.0),
    /// ];
    ///
    /// let polygons = vec![
    ///    Polygon::new(&[0, 1, 2, 4], &vertices).unwrap(), // Safe to unwrap
    /// ];
    ///
    /// let mut mesh = PolyMesh::from(&vertices, &polygons).unwrap(); // Safe to unwrap
    ///
    /// assert_eq!(mesh.vertices().len(), 5);
    /// assert_eq!(mesh.polygons().len(), 1);
    /// assert_eq!(mesh.polygons()[0].vertices(), vec![0, 1, 2, 4]);
    ///
    /// mesh.remove_unused_vertices();
    ///
    /// assert_eq!(mesh.vertices().len(), 4);
    /// assert_eq!(mesh.polygons().len(), 1);
    /// assert_eq!(mesh.polygons()[0].vertices(), vec![0, 1, 2, 3]);
    /// ```
    pub fn remove_unused_vertices(&mut self) {
        let mut new_vertices = Vec::new();
        let mut new_polygons = Vec::new();

        let mut indices: Vec<_> = self.polygons.iter().flat_map(|p| &p.vertices).collect();
        indices.sort();
        indices.dedup();

        indices.iter().for_each(|&&i| {
            new_vertices.push(self.vertices[i]);
        });

        self.polygons.iter().for_each(|p| {
            new_polygons.push(
                Polygon::new(
                    &p.vertices
                        .iter()
                        .map(|i| indices.binary_search(&i).unwrap())
                        .collect::<Vec<usize>>(),
                    &new_vertices,
                )
                .unwrap(),
            );
        });

        self.vertices = new_vertices;
        self.polygons = new_polygons;
    }

    /// Flip the normal of the polygon at the given index. This method is in-place.
    /// This method is useful for meshes containing concave polygons, as they may have
    /// flipped normals.
    ///
    /// # Arguments
    /// * `index` - The index of the polygon to flip.
    ///
    /// # Examples
    /// ```
    /// use phys_engine::geometry::polymesh::PolyMesh;
    /// use ultraviolet::Vec3;
    ///
    /// let mut mesh = PolyMesh::new();
    ///
    /// mesh.add_polygon(&vec![
    ///     Vec3::new(0.0, 0.0, 0.0),
    ///     Vec3::new(1.0, 0.0, 0.0),
    ///     Vec3::new(1.0, 1.0, 0.0),
    ///     Vec3::new(0.0, 1.0, 0.0)
    /// ]);
    ///
    /// mesh.flip_normal(0);
    ///
    /// assert_eq!(mesh.polygons()[0].normal(), Vec3::new(0.0, 0.0, -1.0));
    /// ```
    pub fn flip_normal(&mut self, index: usize) {
        self.polygons[index].normal = -self.polygons[index].normal;
    }

    /// Make a [`TriMesh`] from the [`PolyMesh`].
    /// FIXME: This method is not implemented yet.
    pub fn into_tri_mesh(&self) -> TriMesh {
        todo!("PolyMesh::into_tri_mesh");
    }
}

#[cfg(test)]
mod tests {
    // TODO: Update for new PolyMesh
    #[test]
    fn test_tri_mesh_dedup() {
        use super::TriMesh;
        use ultraviolet::Vec3;

        let epsilon = 0.1;

        let mut mesh = TriMesh::new();

        mesh.add_triangle([
            Vec3::new(0.0, 0.0, 0.0),
            Vec3::new(1.0, 0.0, 0.0),
            Vec3::new(0.0, 1.0, 0.0),
        ]);

        mesh.add_triangle([
            Vec3::new(0.0, 0.0, 0.0),
            Vec3::new(1.0, 0.0, 0.0),
            Vec3::new(0.0, 1.0, 0.0),
        ]);

        mesh.dedup_vertices(epsilon);

        assert_eq!(mesh.vertices().len(), 3);

        assert_eq!(mesh.triangles()[0].vertices(), &[0, 1, 2]);
        assert_eq!(mesh.triangles()[1].vertices(), &[0, 1, 2]);
    }
}
