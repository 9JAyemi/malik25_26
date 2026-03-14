module Arithmetic_Logic_Unit_sva (
    input logic [4:0]  ctrl,
    input logic [15:0] data_in_A,
    input logic [15:0] data_in_B,
    input logic [15:0] data_out
);
    // ctrl=1: output is A + B
    check_add: assert property (
        @(posedge ctrl[0]) disable iff (1'b0) (ctrl == 5'd1) |-> (data_out == (data_in_A + data_in_B))
    );
    // ctrl=2: output is A - B
    check_sub: assert property (
        @(posedge ctrl[0]) disable iff (1'b0) (ctrl == 5'd2) |-> (data_out == (data_in_A - data_in_B))
    );
    // ctrl=3: output is A & B
    check_and: assert property (
        @(posedge ctrl[0]) disable iff (1'b0) (ctrl == 5'd3) |-> (data_out == (data_in_A & data_in_B))
    );
    // ctrl=4: output is A | B
    check_or: assert property (
        @(posedge ctrl[0]) disable iff (1'b0) (ctrl == 5'd4) |-> (data_out == (data_in_A | data_in_B))
    );
    // ctrl=5: output is A ^ B
    check_xor: assert property (
        @(posedge ctrl[0]) disable iff (1'b0) (ctrl == 5'd5) |-> (data_out == (data_in_A ^ data_in_B))
    );
    // ctrl=6: output is ~A
    check_not_a: assert property (
        @(posedge ctrl[0]) disable iff (1'b0) (ctrl == 5'd6) |-> (data_out == (~data_in_A))
    );
    // ctrl=7: output is ~B
    check_not_b: assert property (
        @(posedge ctrl[0]) disable iff (1'b0) (ctrl == 5'd7) |-> (data_out == (~data_in_B))
    );
    // ctrl=8: output is A << 1
    check_shl_a1: assert property (
        @(posedge ctrl[0]) disable iff (1'b0) (ctrl == 5'd8) |-> (data_out == (data_in_A << 1))
    );
    // ctrl=9: output is A >> 1
    check_shr_a1: assert property (
        @(posedge ctrl[0]) disable iff (1'b0) (ctrl == 5'd9) |-> (data_out == (data_in_A >> 1))
    );
    // ctrl=10: output is B << 1
    check_shl_b1: assert property (
        @(posedge ctrl[0]) disable iff (1'b0) (ctrl == 5'd10) |-> (data_out == (data_in_B << 1))
    );
    // ctrl=11: output is B >> 1
    check_shr_b1: assert property (
        @(posedge ctrl[0]) disable iff (1'b0) (ctrl == 5'd11) |-> (data_out == (data_in_B >> 1))
    );
    // ctrl=12: output is (A==B) ? 1 : 0
    check_eq: assert property (
        @(posedge ctrl[0]) disable iff (1'b0) (ctrl == 5'd12) |-> (data_out == ((data_in_A == data_in_B) ? 16'h0001 : 16'h0000))
    );
    // ctrl=13: output is (A<B) ? 1 : 0
    check_lt: assert property (
        @(posedge ctrl[0]) disable iff (1'b0) (ctrl == 5'd13) |-> (data_out == ((data_in_A < data_in_B) ? 16'h0001 : 16'h0000))
    );
    // ctrl=14: output is (A>B) ? 1 : 0
    check_gt: assert property (
        @(posedge ctrl[0]) disable iff (1'b0) (ctrl == 5'd14) |-> (data_out == ((data_in_A > data_in_B) ? 16'h0001 : 16'h0000))
    );
    // ctrl=15: output is (A<=B) ? 1 : 0
    check_le: assert property (
        @(posedge ctrl[0]) disable iff (1'b0) (ctrl == 5'd15) |-> (data_out == ((data_in_A <= data_in_B) ? 16'h0001 : 16'h0000))
    );
    // ctrl=16: output is (A>=B) ? 1 : 0
    check_ge: assert property (
        @(posedge ctrl[0]) disable iff (1'b0) (ctrl == 5'd16) |-> (data_out == ((data_in_A >= data_in_B) ? 16'h0001 : 16'h0000))
    );
    // ctrl not in 1..16: output is 0
    check_default_zero: assert property (
        @(posedge ctrl[0]) disable iff (1'b0) ((ctrl == 5'd0) || (ctrl > 5'd16)) |-> (data_out == 16'h0000)
    );
endmodule