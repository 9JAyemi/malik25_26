
module top_module ( 
    input wire [3:0] in_vec,
    output wire [3:0] out_vec,
    output wire msb_out,
    output wire mid_out,
    output wire lsb_out );
    
    wire [3:0] adder_out;
    
    // Ripple carry adder
    full_adder fa0 (.a(in_vec[0]), .b(1'b0), .cin(1'b0), .sum(adder_out[0]));
    full_adder fa1 (.a(in_vec[1]), .b(adder_out[0]), .cin(1'b0), .sum(adder_out[1]));
    full_adder fa2 (.a(in_vec[2]), .b(adder_out[1]), .cin(1'b0), .sum(adder_out[2]));
    full_adder fa3 (.a(in_vec[3]), .b(adder_out[2]), .cin(1'b0), .sum(adder_out[3]));
    
    // Multiplexer
    assign out_vec = adder_out;
    assign msb_out = in_vec[3];
    assign mid_out = in_vec[1];
    assign lsb_out = in_vec[0];
    
endmodule

module full_adder (
    input a, 
    input b, 
    input cin, 
    output sum);
    
    assign sum = a ^ b ^ cin;
endmodule
