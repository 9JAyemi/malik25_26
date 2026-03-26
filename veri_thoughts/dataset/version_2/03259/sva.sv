module UDM_2x2_sva (
    input logic clk,
    input logic [1:0] in1,
    input logic [1:0] in2,
    input logic [2:0] res
);

    // in1=00 always produces zero.
    check_in1_zero_forces_zero: assert property (
        @(posedge clk) (in1 == 2'b00) |-> (res == 3'b000)
    );

    // in2=00 always produces zero.
    check_in2_zero_forces_zero: assert property (
        @(posedge clk) (in2 == 2'b00) |-> (res == 3'b000)
    );

    // in1=01 maps res to zero-extended in2.
    check_in1_one_maps_in2_direct: assert property (
        @(posedge clk) (in1 == 2'b01) |-> (res == {1'b0, in2})
    );

    // in1=10 maps res to in2 shifted left by one.
    check_in1_two_maps_in2_shifted: assert property (
        @(posedge clk) (in1 == 2'b10) |-> (res == {in2, 1'b0})
    );

    // in1=11 and in2=00 produces zero.
    check_in1_three_in2_zero: assert property (
        @(posedge clk) ((in1 == 2'b11) && (in2 == 2'b00)) |-> (res == 3'b000)
    );

    // in1=11 and in2=01 produces 110.
    check_in1_three_in2_one: assert property (
        @(posedge clk) ((in1 == 2'b11) && (in2 == 2'b01)) |-> (res == 3'b110)
    );

    // in1=11 and in2=10 produces 011.
    check_in1_three_in2_two: assert property (
        @(posedge clk) ((in1 == 2'b11) && (in2 == 2'b10)) |-> (res == 3'b011)
    );

    // in1=11 and in2=11 produces 111.
    check_in1_three_in2_three: assert property (
        @(posedge clk) ((in1 == 2'b11) && (in2 == 2'b11)) |-> (res == 3'b111)
    );

endmodule