
module xor_inv_multiplexer (
    input clk,
    input [3:0] a,
    input [3:0] b,
    input sel_b1,
    input sel_b2,
    input sel_out,
    output reg out_always,
    output [3:0] out_xor,
    output [3:0] out_xor_inv,
    output out_logical_inv
);

    // Intermediate wires to store the selected input
    wire [3:0] selected_input_b1;
    wire [3:0] selected_input_b2;
    
    // 2-to-1 multiplexer to select between a and b
    assign selected_input_b1 = sel_b1 ? b : a;
    
    // 2-to-1 multiplexer to select between selected_input_b1 and b
    assign selected_input_b2 = sel_b2 ? b : selected_input_b1;
    
    // XOR and inverter operations on the selected input
    assign out_xor = selected_input_b2 ^ a;
    assign out_xor_inv = ~out_xor;
    assign out_logical_inv = !out_xor;
  
    // 2-to-1 multiplexer to select between XOR and logical inverse outputs
    always @(posedge clk) begin
        if (sel_out) begin
            out_always <= out_logical_inv;
        end else begin
            out_always <= out_xor_inv;
        end
    end

endmodule