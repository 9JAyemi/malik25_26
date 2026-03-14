module alt_ctl_sva (
    input logic clk,
    input logic [5:0] op,
    input logic [5:0] func,
    input logic [4:0] aluc
);
    // aluc is always within 0..14 per decode table.
    check_aluc_range: assert property (
        @(posedge clk) (aluc <= 5'd14)
    );

    ///// R-type (op == 6'b000000) /////
    // R-type func 100000 maps to 0.
    map_op0_func_100000_to_0: assert property (
        @(posedge clk) (op == 6'b000000 && func == 6'b100000) |-> (aluc == 5'd0)
    );
    // R-type func 100001 maps to 1.
    map_op0_func_100001_to_1: assert property (
        @(posedge clk) (op == 6'b000000 && func == 6'b100001) |-> (aluc == 5'd1)
    );
    // R-type func 100010 maps to 2.
    map_op0_func_100010_to_2: assert property (
        @(posedge clk) (op == 6'b000000 && func == 6'b100010) |-> (aluc == 5'd2)
    );
    // R-type func 100011 maps to 3.
    map_op0_func_100011_to_3: assert property (
        @(posedge clk) (op == 6'b000000 && func == 6'b100011) |-> (aluc == 5'd3)
    );
    // R-type func 100100 maps to 4.
    map_op0_func_100100_to_4: assert property (
        @(posedge clk) (op == 6'b000000 && func == 6'b100100) |-> (aluc == 5'd4)
    );
    // R-type func 100101 maps to 5.
    map_op0_func_100101_to_5: assert property (
        @(posedge clk) (op == 6'b000000 && func == 6'b100101) |-> (aluc == 5'd5)
    );
    // R-type func 100110 maps to 6.
    map_op0_func_100110_to_6: assert property (
        @(posedge clk) (op == 6'b000000 && func == 6'b100110) |-> (aluc == 5'd6)
    );
    // R-type func 100111 maps to 7.
    map_op0_func_100111_to_7: assert property (
        @(posedge clk) (op == 6'b000000 && func == 6'b100111) |-> (aluc == 5'd7)
    );
    // R-type func 101010 maps to 8.
    map_op0_func_101010_to_8: assert property (
        @(posedge clk) (op == 6'b000000 && func == 6'b101010) |-> (aluc == 5'd8)
    );
    // R-type func 101011 maps to 9.
    map_op0_func_101011_to_9: assert property (
        @(posedge clk) (op == 6'b000000 && func == 6'b101011) |-> (aluc == 5'd9)
    );
    // R-type func 000000 maps to 10.
    map_op0_func_000000_to_10: assert property (
        @(posedge clk) (op == 6'b000000 && func == 6'b000000) |-> (aluc == 5'd10)
    );
    // R-type func 000010 maps to 11.
    map_op0_func_000010_to_11: assert property (
        @(posedge clk) (op == 6'b000000 && func == 6'b000010) |-> (aluc == 5'd11)
    );
    // R-type func 000011 maps to 12.
    map_op0_func_000011_to_12: assert property (
        @(posedge clk) (op == 6'b000000 && func == 6'b000011) |-> (aluc == 5'd12)
    );
    // R-type func 000100 maps to 10.
    map_op0_func_000100_to_10: assert property (
        @(posedge clk) (op == 6'b000000 && func == 6'b000100) |-> (aluc == 5'd10)
    );
    // R-type func 000110 maps to 11.
    map_op0_func_000110_to_11: assert property (
        @(posedge clk) (op == 6'b000000 && func == 6'b000110) |-> (aluc == 5'd11)
    );
    // R-type func 000111 maps to 12.
    map_op0_func_000111_to_12: assert property (
        @(posedge clk) (op == 6'b000000 && func == 6'b000111) |-> (aluc == 5'd12)
    );
    // R-type func 000001 maps to 13.
    map_op0_func_000001_to_13: assert property (
        @(posedge clk) (op == 6'b000000 && func == 6'b000001) |-> (aluc == 5'd13)
    );
    // R-type default (unlisted func) maps to 0.
    map_op0_default_func_to_0: assert property (
        @(posedge clk) (op == 6'b000000 && !(func inside {
            6'b100000,6'b100001,6'b100010,6'b100011,6'b100100,6'b100101,6'b100110,6'b100111,
            6'b101010,6'b101011,6'b000000,6'b000010,6'b000011,6'b000100,6'b000110,6'b000111,6'b000001
        })) |-> (aluc == 5'd0)
    );

    ///// I-type (op != 6'b000000) /////
    // I-type op 001000 maps to 0.
    map_op_001000_to_0: assert property (
        @(posedge clk) (op == 6'b001000) |-> (aluc == 5'd0)
    );
    // I-type op 001001 maps to 1.
    map_op_001001_to_1: assert property (
        @(posedge clk) (op == 6'b001001) |-> (aluc == 5'd1)
    );
    // I-type op 001100 maps to 4.
    map_op_001100_to_4: assert property (
        @(posedge clk) (op == 6'b001100) |-> (aluc == 5'd4)
    );
    // I-type op 001101 maps to 5.
    map_op_001101_to_5: assert property (
        @(posedge clk) (op == 6'b001101) |-> (aluc == 5'd5)
    );
    // I-type op 001110 maps to 6.
    map_op_001110_to_6: assert property (
        @(posedge clk) (op == 6'b001110) |-> (aluc == 5'd6)
    );
    // I-type op 001010 maps to 8.
    map_op_001010_to_8: assert property (
        @(posedge clk) (op == 6'b001010) |-> (aluc == 5'd8)
    );
    // I-type op 001011 maps to 9.
    map_op_001011_to_9: assert property (
        @(posedge clk) (op == 6'b001011) |-> (aluc == 5'd9)
    );
    // I-type op 001111 maps to 14.
    map_op_001111_to_14: assert property (
        @(posedge clk) (op == 6'b001111) |-> (aluc == 5'd14)
    );
    // I-type default (unlisted op and not R-type) maps to 0.
    map_default_other_ops_to_0: assert property (
        @(posedge clk) ((op != 6'b000000) && !(op inside {
            6'b001000,6'b001001,6'b001100,6'b001101,6'b001110,6'b001010,6'b001011,6'b001111
        })) |-> (aluc == 5'd0)
    );

    ///// Generic decode sanity /////
    // If op and func are stable across cycles, aluc remains stable.
    stable_when_inputs_stable: assert property (
        @(posedge clk) ($stable(op) && $stable(func)) |-> $stable(aluc)
    );

endmodule