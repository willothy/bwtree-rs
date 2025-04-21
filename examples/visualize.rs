use bwtree::{visualization::BwTreeVisualize, BwTreeMap};
use std::env;

fn main() -> std::io::Result<()> {
    let args: Vec<String> = env::args().collect();
    let output_file = args.get(1).map(|s| s.as_str()).unwrap_or("bwtree.dot");
    
    println!("Creating BwTree visualization...");
    
    // Create a new BwTree
    let tree = BwTreeMap::<i32, String>::new();
    
    // Insert some values
    for i in 1..100 {
        tree.insert(i, format!("value_{}", i));
        
        // Delete some values to create delete deltas
        if i % 5 == 0 {
            tree.delete(i - 2);
        }
        
        // Update some values
        if i % 10 == 0 {
            tree.insert(i / 2, format!("updated_value_{}", i / 2));
        }
    }
    
    // Generate and save the DOT file
    tree.save_visualization(output_file)?;
    println!("Visualization saved to {}", output_file);
    
    // If GraphViz is installed, also generate a PNG
    if let Some(png_file) = output_file.strip_suffix(".dot").map(|s| format!("{}.png", s)) {
        match bwtree::visualization::generate_image(output_file, &png_file) {
            Ok(_) => println!("PNG visualization saved to {}", png_file),
            Err(e) => println!("Failed to generate PNG (GraphViz may not be installed): {}", e),
        }
    }
    
    println!("\nVisualization complete!");
    println!("To view the visualization:");
    println!("1. Install GraphViz if not already installed");
    println!("2. Run: dot -Tpng {} -o bwtree.png", output_file);
    println!("3. Open bwtree.png with your image viewer");
    
    Ok(())
}