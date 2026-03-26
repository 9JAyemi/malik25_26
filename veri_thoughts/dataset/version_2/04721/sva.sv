module priority_encoder_pipeline_sva (
    input logic [3:0] in,
    input logic clk,
    input logic [1:0] pos
);

    // Bit 3 has highest priority and reaches pos after one clock.
    check_priority_bit3: assert property (
        @(posedge clk) in[3] |=> (pos == 2'b11)
    );

    // Bit 2 selects pos when bit 3 is low, regardless of lower bits.
    check_priority_bit2: assert property (
        @(posedge clk) (!in[3] && in[2]) |=> (pos == 2'b10)
    );

    // Bit 1 selects pos when bits 3 and 2 are low, regardless of bit 0.
    check_priority_bit1: assert property (
        @(posedge clk) ((in[3:2] == 2'b00) && in[1]) |=> (pos == 2'b01)
    );

    // pos is 00 when bits 3, 2, and 1 are all low.
    check_default_zero: assert property (
        @(posedge clk) (in[3:1] == 3'b000) |=> (pos == 2'b00)
    );

endmodule