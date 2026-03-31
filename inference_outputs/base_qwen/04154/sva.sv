```systemverilog
module invert_msb_sva (
    input logic [3:0] i_binary,
    output logic [3:0] o_inverted
);
    // Combinational logic: o_inverted is the inverse of the most significant bit of i_binary, with the rest unchanged.
    invert_msb_behavior: assert property (
        @(posedge CLK) disable iff (!RESETn) (o_inverted == {~i_binary[3], i_binary[2:0]})
    );
endmodule
```