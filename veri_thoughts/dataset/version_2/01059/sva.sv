module magnitude_comparator_sva (
    input logic        valid,
    input logic [3:0]  A,
    input logic [3:0]  B,
    input logic [1:0]  sel,
    input logic [1:0]  out_mode0,
    input logic        less_than,
    input logic        equal_to,
    input logic        greater_than
);
    ///// Mode-0 (magnitude code) behavior /////
    // When sel==00, out_mode0 encodes compare result: 00 if A==B, 01 if A>B, 10 if A<B.
    check_sel00_magnitude_encoding: assert property (
        @(posedge valid) (sel == 2'b00) |-> (out_mode0 == ((A == B) ? 2'b00 : ((A > B) ? 2'b01 : 2'b10)))
    );
    // When sel!=00, out_mode0 must be 00.
    check_sel_not00_out_zero: assert property (
        @(posedge valid) (sel != 2'b00) |-> (out_mode0 == 2'b00)
    );
    // For sel==00, out_mode0[1] reflects (A<B).
    check_sel00_out_msb_is_less: assert property (
        @(posedge valid) (sel == 2'b00) |-> (out_mode0[1] == (A < B))
    );
    // For sel==00, out_mode0[0] reflects (A>B).
    check_sel00_out_lsb_is_greater: assert property (
        @(posedge valid) (sel == 2'b00) |-> (out_mode0[0] == (A > B))
    );

    ///// Mode-1 (flag outputs) behavior /////
    // When sel==01, less_than reflects (A<B).
    check_sel01_less_than_matches: assert property (
        @(posedge valid) (sel == 2'b01) |-> (less_than == (A < B))
    );
    // When sel==01, equal_to reflects (A==B).
    check_sel01_equal_to_matches: assert property (
        @(posedge valid) (sel == 2'b01) |-> (equal_to == (A == B))
    );
    // When sel==01, greater_than reflects (A>B).
    check_sel01_greater_than_matches: assert property (
        @(posedge valid) (sel == 2'b01) |-> (greater_than == (A > B))
    );
    // When sel==01, exactly one of the three flags is HIGH.
    check_sel01_onehot_result: assert property (
        @(posedge valid) (sel == 2'b01) |-> $onehot({less_than, equal_to, greater_than})
    );

    ///// Output gating when not in mode-1 /////
    // When sel!=01, less_than must be 0.
    check_sel_not01_less_zero: assert property (
        @(posedge valid) (sel != 2'b01) |-> (less_than == 1'b0)
    );
    // When sel!=01, equal_to must be 0.
    check_sel_not01_equal_zero: assert property (
        @(posedge valid) (sel != 2'b01) |-> (equal_to == 1'b0)
    );
    // When sel!=01, greater_than must be 0.
    check_sel_not01_greater_zero: assert property (
        @(posedge valid) (sel != 2'b01) |-> (greater_than == 1'b0)
    );
endmodule