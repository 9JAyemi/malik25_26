module priority_encoder_sva (
    input logic [7:0] D,
    input logic [2:0] EN
);
    // EN[2] mirrors D[7] (highest priority)
    check_en2_mirrors_d7: assert property (
        @(posedge D[0]) disable iff (1'b0) (EN[2] == D[7])
    );
    // EN[1] is set iff D[6] is 1 and D[7] is 0
    check_en1_priority: assert property (
        @(posedge D[0]) disable iff (1'b0) (EN[1] == (!D[7] && D[6]))
    );
    // EN[0] is set iff D[5] is 1 and D[7:6] are 0
    check_en0_priority: assert property (
        @(posedge D[0]) disable iff (1'b0) (EN[0] == (!D[7] && !D[6] && D[5]))
    );
    // EN is one-hot or zero
    check_en_onehot0: assert property (
        @(posedge D[0]) disable iff (1'b0) $onehot0(EN)
    );
    // If D7 is 1, EN must be 3'b100
    check_d7_implies_en100: assert property (
        @(posedge D[0]) disable iff (1'b0) D[7] |-> (EN == 3'b100)
    );
    // If D6 is 1 and D7 is 0, EN must be 3'b010
    check_d6_implies_en010: assert property (
        @(posedge D[0]) disable iff (1'b0) (!D[7] && D[6]) |-> (EN == 3'b010)
    );
    // If only D5 among top bits is 1, EN must be 3'b001
    check_d5_implies_en001: assert property (
        @(posedge D[0]) disable iff (1'b0) (!D[7] && !D[6] && D[5]) |-> (EN == 3'b001)
    );
    // If D[7:5]==3'b000, EN must be 3'b000
    check_none_implies_en000: assert property (
        @(posedge D[0]) disable iff (1'b0) (!D[7] && !D[6] && !D[5]) |-> (EN == 3'b000)
    );
    // EN depends only on D[7:5] (stable upper bits imply stable EN)
    check_en_independent_of_low5: assert property (
        @(posedge D[0]) disable iff (1'b0) $stable(D[7:5]) |-> $stable(EN)
    );
endmodule