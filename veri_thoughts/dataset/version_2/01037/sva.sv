module bcd_to_7seg_sva (
    input logic [3:0] BCD,
    input logic a, b, c, d, e, f, g
);
    ///// Combinational mapping checks /////
    // BCD=0 drives 0 on g and 1 on a-f.
    check_bcd_0: assert property (
        @(posedge $global_clock) disable iff (1'b0) (BCD == 4'b0000) |-> (a==1 && b==1 && c==1 && d==1 && e==1 && f==1 && g==0)
    );
    // BCD=1 drives b,c high; others low.
    check_bcd_1: assert property (
        @(posedge $global_clock) disable iff (1'b0) (BCD == 4'b0001) |-> (a==0 && b==1 && c==1 && d==0 && e==0 && f==0 && g==0)
    );
    // BCD=2 mapping per case item.
    check_bcd_2: assert property (
        @(posedge $global_clock) disable iff (1'b0) (BCD == 4'b0010) |-> (a==1 && b==1 && c==0 && d==1 && e==1 && f==0 && g==1)
    );
    // BCD=3 mapping per case item.
    check_bcd_3: assert property (
        @(posedge $global_clock) disable iff (1'b0) (BCD == 4'b0011) |-> (a==1 && b==1 && c==1 && d==1 && e==0 && f==0 && g==1)
    );
    // BCD=4 mapping per case item.
    check_bcd_4: assert property (
        @(posedge $global_clock) disable iff (1'b0) (BCD == 4'b0100) |-> (a==0 && b==1 && c==1 && d==0 && e==0 && f==1 && g==1)
    );
    // BCD=5 mapping per case item.
    check_bcd_5: assert property (
        @(posedge $global_clock) disable iff (1'b0) (BCD == 4'b0101) |-> (a==1 && b==0 && c==1 && d==1 && e==0 && f==1 && g==1)
    );
    // BCD=6 mapping per case item.
    check_bcd_6: assert property (
        @(posedge $global_clock) disable iff (1'b0) (BCD == 4'b0110) |-> (a==1 && b==0 && c==1 && d==1 && e==1 && f==1 && g==1)
    );
    // BCD=7 mapping per case item.
    check_bcd_7: assert property (
        @(posedge $global_clock) disable iff (1'b0) (BCD == 4'b0111) |-> (a==1 && b==1 && c==1 && d==0 && e==0 && f==0 && g==0)
    );
    // BCD=8 mapping per case item.
    check_bcd_8: assert property (
        @(posedge $global_clock) disable iff (1'b0) (BCD == 4'b1000) |-> (a==1 && b==1 && c==1 && d==1 && e==1 && f==1 && g==1)
    );
    // BCD=9 mapping per case item.
    check_bcd_9: assert property (
        @(posedge $global_clock) disable iff (1'b0) (BCD == 4'b1001) |-> (a==1 && b==1 && c==1 && d==1 && e==0 && f==1 && g==1)
    );
    // For non-BCD inputs 10..15, all segments are 0.
    check_invalid_defaults_zero: assert property (
        @(posedge $global_clock) disable iff (1'b0) (BCD inside {[4'd10:4'd15]}) |-> (a==0 && b==0 && c==0 && d==0 && e==0 && f==0 && g==0)
    );
endmodule