module reverse_last_two_bits_sva (
    input logic clk,
    input logic [3:0] in,
    output logic [1:0] out
);
    ///// Sequential logic behavior /////
    // The output out should always be the last two bits of the input in reversed order.
    reverse_last_two_bits: assert property (
        @(posedge clk) $stable(in) |-> out == {in[1:0], in[3:2]}
    );
endmodule