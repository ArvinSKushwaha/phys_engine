//! This module provides useful Geometry utilities, like calculating
//! normals and checking for coplanarity.

use ultraviolet::Vec3;

/// Computes the normal vector to 3 vertices in counter-clockwise order.
///
/// # Arguments
/// * [`v0`] - The first vertex of the triangle.
/// * [`v1`] - The second vertex of the triangle.
/// * [`v2`] - The third vertex of the triangle.
///
/// # Returns
/// A [`Vec3`] object representing the normal vector to the vertices. This function
/// uses the right-hand rule.
///
pub(crate) fn get_normal(v0: Vec3, v1: Vec3, v2: Vec3) -> Vec3 {
    let v1 = v1 - v0;
    let v2 = v2 - v0;
    v1.cross(v2)
}

/// Checks if vertices are coplanar. This is done by checking that each cross product
/// points in the same direction.
///
/// # Arguments
/// * [`vertices`] - A slice of [`Vec3`] points to check for coplanarity.
///
/// # Returns
/// [`true`] if the vertices are coplanar, otherwise [`false`].
pub(crate) fn is_coplanar(vertices: &[Vec3]) -> bool {
    const COPLANARITY_TOLERANCE: f32 = 0.00001;
    // Naive Algorithm, simply check that all cross products are collinear.
    // Should be O(n) which is fast, but also, makes me sad.
    let normal = get_normal(vertices[0], vertices[1], vertices[2]);
    for window in vertices.windows(3) {
        let normal2 = get_normal(window[0], window[1], window[2]);
        if normal2.cross(normal).mag_sq() > COPLANARITY_TOLERANCE {
            return false;
        }
    }
    true
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_get_normals() {
        use super::get_normal;
        use ultraviolet::Vec3;

        let v0 = Vec3::new(0.0, 0.0, 0.0);
        let v1 = Vec3::new(1.0, 0.0, 0.0);
        let v2 = Vec3::new(0.0, 1.0, 0.0);
        let normal = get_normal(v0, v1, v2);

        assert_eq!(normal, Vec3::new(0.0, 0.0, 1.0));
    }

    #[test]
    fn test_is_coplanar() {
        use super::is_coplanar;
        use ultraviolet::Vec3;

        let vertices = vec![
            Vec3::new(0.0, 0.0, 0.0),
            Vec3::new(1.0, 0.0, 0.0),
            Vec3::new(1.0, 1.0, 0.0),
            Vec3::new(0.0, 1.0, 0.0),
        ];

        assert!(is_coplanar(&vertices));
    }
}
