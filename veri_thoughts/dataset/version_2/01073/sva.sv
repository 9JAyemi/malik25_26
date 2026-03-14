module alt_ctl_sva (
    input logic CLK,        // External clock for SVA
    input logic RESETn,     // External active-low reset for SVA gating
    input logic [5:0] op,
    input logic [5:0] func,
    input logic [4:0] aluc
);
    // Analysis: RTL has no clock/reset and is purely combinational (always @*); this module uses external CLK/RESETn only to clock/gate assertions.

    ///// General range /////
    // aluc must be within 0..14 as all assignments are in this range.
    check_aluc_range: assert property (
        @(posedge CLK) disable iff (!RESETn) (aluc <= 5'd14)
    );

    ///// Outer op decode (direct mappings) /////
    // When op == 000000, aluc must be 0.
    check_op_000000_aluc0: assert property (
        @(posedge CLK) disable iff (!RESETn) (op == 6'b000000) |-> (aluc == 5'd0)
    );
    // When op == 000001, aluc must be 1.
    check_op_000001_aluc1: assert property (
        @(posedge CLK) disable iff (!RESETn) (op == 6'b000001) |-> (aluc == 5'd1)
    );
    // When op == 000010, aluc must be 2.
    check_op_000010_aluc2: assert property (
        @(posedge CLK) disable iff (!RESETn) (op == 6'b000010) |-> (aluc == 5'd2)
    );
    // When op == 000011, aluc must be 3.
    check_op_000011_aluc3: assert property (
        @(posedge CLK) disable iff (!RESETn) (op == 6'b000011) |-> (aluc == 5'd3)
    );
    // When op == 000100, aluc must be 5.
    check_op_000100_aluc5: assert property (
        @(posedge CLK) disable iff (!RESETn) (op == 6'b000100) |-> (aluc == 5'd5)
    );
    // When op == 000101, aluc must be 14.
    check_op_000101_aluc14: assert property (
        @(posedge CLK) disable iff (!RESETn) (op == 6'b000101) |-> (aluc == 5'd14)
    );
    // When op == 001001, aluc must be 1.
    check_op_001001_aluc1: assert property (
        @(posedge CLK) disable iff (!RESETn) (op == 6'b001001) |-> (aluc == 5'd1)
    );
    // When op == 001010, aluc must be 13.
    check_op_001010_aluc13: assert property (
        @(posedge CLK) disable iff (!RESETn) (op == 6'b001010) |-> (aluc == 5'd13)
    );
    // For any op not explicitly listed (and not 001000), aluc must be 0 (outer default).
    check_default_other_ops_aluc0: assert property (
        @(posedge CLK) disable iff (!RESETn)
            (!(op inside {6'b001000,6'b000000,6'b000001,6'b000010,6'b000011,6'b000100,6'b000101,6'b001001,6'b001010})) |-> (aluc == 5'd0)
    );

    ///// Inner func decode when op == 001000 /////
    // func 100000 -> aluc 0
    check_op001000_func100000_aluc0: assert property (
        @(posedge CLK) disable iff (!RESETn) (op == 6'b001000 && func == 6'b100000) |-> (aluc == 5'd0)
    );
    // func 100010 -> aluc 1
    check_op001000_func100010_aluc1: assert property (
        @(posedge CLK) disable iff (!RESETn) (op == 6'b001000 && func == 6'b100010) |-> (aluc == 5'd1)
    );
    // func 100100 -> aluc 2
    check_op001000_func100100_aluc2: assert property (
        @(posedge CLK) disable iff (!RESETn) (op == 6'b001000 && func == 6'b100100) |-> (aluc == 5'd2)
    );
    // func 100101 -> aluc 3
    check_op001000_func100101_aluc3: assert property (
        @(posedge CLK) disable iff (!RESETn) (op == 6'b001000 && func == 6'b100101) |-> (aluc == 5'd3)
    );
    // func 100110 -> aluc 4
    check_op001000_func100110_aluc4: assert property (
        @(posedge CLK) disable iff (!RESETn) (op == 6'b001000 && func == 6'b100110) |-> (aluc == 5'd4)
    );
    // func 101010 -> aluc 5
    check_op001000_func101010_aluc5: assert property (
        @(posedge CLK) disable iff (!RESETn) (op == 6'b001000 && func == 6'b101010) |-> (aluc == 5'd5)
    );
    // func 000000 -> aluc 6
    check_op001000_func000000_aluc6: assert property (
        @(posedge CLK) disable iff (!RESETn) (op == 6'b001000 && func == 6'b000000) |-> (aluc == 5'd6)
    );
    // func 000100 -> aluc 7
    check_op001000_func000100_aluc7: assert property (
        @(posedge CLK) disable iff (!RESETn) (op == 6'b001000 && func == 6'b000100) |-> (aluc == 5'd7)
    );
    // func 000011 -> aluc 8
    check_op001000_func000011_aluc8: assert property (
        @(posedge CLK) disable iff (!RESETn) (op == 6'b001000 && func == 6'b000011) |-> (aluc == 5'd8)
    );
    // func 000111 -> aluc 9
    check_op001000_func000111_aluc9: assert property (
        @(posedge CLK) disable iff (!RESETn) (op == 6'b001000 && func == 6'b000111) |-> (aluc == 5'd9)
    );
    // func 000110 -> aluc 11
    check_op001000_func000110_aluc11: assert property (
        @(posedge CLK) disable iff (!RESETn) (op == 6'b001000 && func == 6'b000110) |-> (aluc == 5'd11)
    );
    // func 000001 -> aluc 12
    check_op001000_func000001_aluc12: assert property (
        @(posedge CLK) disable iff (!RESETn) (op == 6'b001000 && func == 6'b000001) |-> (aluc == 5'd12)
    );
    // func 011011 -> aluc 14
    check_op001000_func011011_aluc14: assert property (
        @(posedge CLK) disable iff (!RESETn) (op == 6'b001000 && func == 6'b011011) |-> (aluc == 5'd14)
    );
    // For op==001000 and any func not listed in the case items, aluc must be 0 (inner default).
    check_op001000_default_other_funcs_aluc0: assert property (
        @(posedge CLK) disable iff (!RESETn)
            (op == 6'b001000 && !(func inside {6'b100000,6'b100010,6'b100100,6'b100101,6'b100110,6'b101010,6'b000000,6'b000100,6'b000011,6'b000111,6'b000010,6'b000110,6'b000001,6'b011011})) |-> (aluc == 5'd0)
    );

endmodule