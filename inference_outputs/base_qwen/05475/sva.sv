```systemverilog
module barrel_shifter_sva (
    input logic clk,
    input logic rst_n,
    input logic [3:0] in,
    input logic [1:0] shift_amt,
    input logic dir,
    output logic [3:0] out
);
    // Sequential logic is not present, so use @(posedge clk) for assertions.

    // Check that the output is correctly set based on the shift amount and direction
    property p_shift;
        @(posedge clk) disable iff (!rst_n) 
        (shift_amt == 2'b00) |-> (out == in) ||
        (shift_amt == 2'b01) |-> (out == (dir == 1) ? {in[2:0], in[3]} : {in[1:0], in[3:2]}) ||
        (shift_amt == 2'b10) |-> (out == (dir == 1) ? {in[1:0], in[3:2]} : {in[2:0], in[3]}) ||
        (shift_amt == 2'b11) |-> (out == {in[0], in[3:1]});
    endproperty
    assert property (p_shift) else $error("Shift operation does not match expected output.");

    // Check that the output is not driven during reset
    property p_reset;
        @(posedge clk) disable iff (!rst_n) 
        rst_n |-> out == 4'b0000;
    endproperty
    assert property (p_reset) else $error("Output is driven during reset.");

endmodule
```