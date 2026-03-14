module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [7:0] a1,
    input logic [7:0] b1,
    input logic [7:0] a2,
    input logic [7:0] b2,
    input logic EN,
    input logic [2:0] Y
);

    ///// Helper expressions (expanded inline in properties) /////
    // p1 = ({8'b0,$past(a1)} * {8'b0,$past(b1)})[15:0]
    // p2 = ({8'b0,$past(a2)} * {8'b0,$past(b2)})[15:0]

    ///// Reset behavior /////
    // After a cycle with reset=1, priority encoder must see zeros -> EN=0 and Y=000.
    check_reset_clears_outputs_next: assert property (
        @(posedge clk) disable iff (reset)
            $past(reset) |-> (EN == 1'b0 && Y == 3'b000)
    );

    ///// EN behavior /////
    // EN must be 0 when both products are zero.
    check_en_low_when_both_zero: assert property (
        @(posedge clk) disable iff (reset)
            ((({8'b0,$past(a1)} * {8'b0,$past(b1)})[15:0] == 16'h0000) &&
             (({8'b0,$past(a2)} * {8'b0,$past(b2)})[15:0] == 16'h0000))
            |-> (EN == 1'b0)
    );

    // EN must be 1 when at least one product is nonzero.
    check_en_high_when_any_nonzero: assert property (
        @(posedge clk) disable iff (reset)
            ((({8'b0,$past(a1)} * {8'b0,$past(b1)})[15:0] != 16'h0000) ||
             (({8'b0,$past(a2)} * {8'b0,$past(b2)})[15:0] != 16'h0000))
            |-> (EN == 1'b1)
    );

    ///// Y behavior for zero case /////
    // Y must be 000 when both products are zero.
    check_y_zero_when_both_zero: assert property (
        @(posedge clk) disable iff (reset)
            ((({8'b0,$past(a1)} * {8'b0,$past(b1)})[15:0] == 16'h0000) &&
             (({8'b0,$past(a2)} * {8'b0,$past(b2)})[15:0] == 16'h0000))
            |-> (Y == 3'b000)
    );

    ///// Selection behavior /////
    // When product1 > product2, select product1[12:10] and EN=1.
    check_select_p1_when_greater: assert property (
        @(posedge clk) disable iff (reset)
            (({8'b0,$past(a1)} * {8'b0,$past(b1)})[15:0] >
             ({8'b0,$past(a2)} * {8'b0,$past(b2)})[15:0])
            |-> (EN == 1'b1 && Y == ({8'b0,$past(a1)} * {8'b0,$past(b1)})[12:10])
    );

    // When product2 > product1, select product2[12:10] and EN=1.
    check_select_p2_when_greater: assert property (
        @(posedge clk) disable iff (reset)
            (({8'b0,$past(a2)} * {8'b0,$past(b2)})[15:0] >
             ({8'b0,$past(a1)} * {8'b0,$past(b1)})[15:0])
            |-> (EN == 1'b1 && Y == ({8'b0,$past(a2)} * {8'b0,$past(b2)})[12:10])
    );

    // When products are equal and nonzero, select product2[12:10] and EN=1.
    check_select_p2_when_equal_nonzero: assert property (
        @(posedge clk) disable iff (reset)
            ((({8'b0,$past(a1)} * {8'b0,$past(b1)})[15:0] ==
              ({8'b0,$past(a2)} * {8'b0,$past(b2)})[15:0]) &&
             (({8'b0,$past(a1)} * {8'b0,$past(b1)})[15:0] != 16'h0000))
            |-> (EN == 1'b1 && Y == ({8'b0,$past(a2)} * {8'b0,$past(b2)})[12:10])
    );

    // When only product1 is nonzero, select product1[12:10] and EN=1.
    check_select_p1_when_only_p1_nonzero: assert property (
        @(posedge clk) disable iff (reset)
            ((({8'b0,$past(a1)} * {8'b0,$past(b1)})[15:0] != 16'h0000) &&
             (({8'b0,$past(a2)} * {8'b0,$past(b2)})[15:0] == 16'h0000))
            |-> (EN == 1'b1 && Y == ({8'b0,$past(a1)} * {8'b0,$past(b1)})[12:10])
    );

    // When only product2 is nonzero, select product2[12:10] and EN=1.
    check_select_p2_when_only_p2_nonzero: assert property (
        @(posedge clk) disable iff (reset)
            ((({8'b0,$past(a2)} * {8'b0,$past(b2)})[15:0] != 16'h0000) &&
             (({8'b0,$past(a1)} * {8'b0,$past(b1)})[15:0] == 16'h0000))
            |-> (EN == 1'b1 && Y == ({8'b0,$past(a2)} * {8'b0,$past(b2)})[12:10])
    );

    // When EN==1, Y must reflect the selected product's [12:10] and at least one product nonzero.
    check_en1_implies_consistent_y: assert property (
        @(posedge clk) disable iff (reset)
            EN == 1'b1 |-> 
                ( (({8'b0,$past(a1)} * {8'b0,$past(b1)})[15:0] != 16'h0000) ||
                  (({8'b0,$past(a2)} * {8'b0,$past(b2)})[15:0] != 16'h0000) )
                &&
                ( Y == ( (({8'b0,$past(a1)} * {8'b0,$past(b1)})[15:0] >
                          ({8'b0,$past(a2)} * {8'b0,$past(b2)})[15:0])
                        ? ({8'b0,$past(a1)} * {8'b0,$past(b1)})[12:10]
                        : ({8'b0,$past(a2)} * {8'b0,$past(b2)})[12:10] ) )
    );

endmodule