use std::env;
use std::process::exit;

use graph_project::Graph;

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() <= 2 || args.len() > 3 { /* it meand run app without args or wrong args */
        println!("usage: ./app --help to show this message\n       ./app --file file.tgf to print graph");
        exit(1);
    }

    if args.len() == 3 {
        if args[1] == "--file" && args[2].len() > 4 {
            match Graph::<String>::deserialize_from_tgf(args[2].as_str()) {
                Ok(graph) => {
                    let mut buffer = String::with_capacity(4096);

                    for vertex in &graph.vertices {
                        buffer.push_str(format!("Vertex: {}\n", vertex.id).as_str());
                        buffer.push_str(format!("Adjacent vertices:").as_str());

                        for edge in graph.edges.iter().filter(|e| e.start == vertex.id) {
                            buffer.push_str(format!("  {}", edge.end).as_str());
                        }
                        buffer.push_str(format!("\nValue: {:?}", vertex.value).as_str());
                        println!("{}\n", buffer);
                        buffer.clear();
                    }
                }
                Err(err) => {
                    eprint!("parsing error: {}", err);
                    exit(2)
                }
            }
        } else {
            println!("usage: ./app --help to show this message\n       ./app --file file.tgf to print graph");
            exit(1);
        }
    }
    exit(0);
}
