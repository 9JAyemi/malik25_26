```systemverilog
module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [7:0] d,
    input logic a, b, c,
    output logic [7:0] q
);
    wire [3:0] mux_out;
    wire [7:0] flip_flops_out;
    
    multiplexer mux (
        .a(a),
        .b(b),
        .c(c),
        .out(mux_out)
    );
    
    flip_flops ff (
        .clk(clk),
        .reset(reset),
        .d(d),
        .q(flip_flops_out)
    );
    
    assign q = mux_out & flip_flops_out;
    
    ///// Multiplexer behavior /////
    // Mux output should be one of the predefined values based on inputs a, b, c.
    mux_output: assert property (
        @(posedge clk) disable iff (!reset) (mux_out inside {4'b0001, 4'b0010, 4'b0100, 4'b1000, 4'b0011, 4'b0110, 4'b1100, 4'b1111})
    );
    
    ///// Flip-flops behavior /////
    // Flip-flops output should be equal to d after 4 clock cycles.
    flip_flops_output: assert property (
        @(posedge clk) disable iff (!reset) (flip_flops_out == d) |-> (counter == 3'b111)
    );
    
    ///// Combined behavior /////
    // Output should be the AND of mux_out and flip_flops_out.
    combined_output: assert property (
        @(posedge clk) disable iff (!reset) (q == (mux_out & flip_flops_out))
    );
endmodule
```