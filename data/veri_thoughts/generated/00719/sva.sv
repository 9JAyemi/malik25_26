module two_bit_encoder_sva (
    input logic clk,
    input logic [1:0] data,
    input logic q,
    input logic zero
);
    // q is the bitwise complement of data[0].
    check_q_complement_data0: assert property (
        @(posedge clk) q == ~data[0]
    );
    // zero is NOR of data[1:0].
    check_zero_is_nor: assert property (
        @(posedge clk) zero == ~(data[0] | data[1])
    );
    // zero high implies q high (since data==2'b00).
    check_zero_implies_q: assert property (
        @(posedge clk) zero |-> (q == 1'b1)
    );
    // Any data bit high forces zero low.
    check_any_data_one_forces_zero_low: assert property (
        @(posedge clk) (data[0] | data[1]) |-> (zero == 1'b0)
    );
    // zero equals q AND not data[1].
    check_zero_equals_q_and_not_data1: assert property (
        @(posedge clk) zero == (q & ~data[1])
    );
    // q and data[0] are never both 1.
    check_q_data0_mutex: assert property (
        @(posedge clk) !(q & data[0])
    );
    // Truth table: data==2'b00 => q=1, zero=1.
    check_tt_00: assert property (
        @(posedge clk) (data == 2'b00) |-> (q == 1'b1 && zero == 1'b1)
    );
    // Truth table: data==2'b01 => q=0, zero=0.
    check_tt_01: assert property (
        @(posedge clk) (data == 2'b01) |-> (q == 1'b0 && zero == 1'b0)
    );
    // Truth table: data==2'b10 => q=1, zero=0.
    check_tt_10: assert property (
        @(posedge clk) (data == 2'b10) |-> (q == 1'b1 && zero == 1'b0)
    );
    // Truth table: data==2'b11 => q=0, zero=0.
    check_tt_11: assert property (
        @(posedge clk) (data == 2'b11) |-> (q == 1'b0 && zero == 1'b0)
    );
endmodule