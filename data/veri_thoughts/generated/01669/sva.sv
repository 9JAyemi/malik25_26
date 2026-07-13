module add_sub_mux_sva (
    input logic clk,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic mode,
    input logic [3:0] B,
    input logic [3:0] C,
    input logic [3:0] D,
    input logic [3:0] E,
    input logic [1:0] SEL,
    input logic EN,
    input logic [3:0] q
);
    ///// Mux behavior /////
    // EN low forces q to E regardless of SEL.
    check_en_low_selects_E: assert property (
        @(posedge clk) disable iff (1'b0) (!EN) |-> (q == E)
    );

    // With EN high and SEL==01, q == B.
    check_en_high_sel_01_B: assert property (
        @(posedge clk) disable iff (1'b0) (EN && (SEL == 2'b01)) |-> (q == B)
    );

    // With EN high and SEL==10, q == C.
    check_en_high_sel_10_C: assert property (
        @(posedge clk) disable iff (1'b0) (EN && (SEL == 2'b10)) |-> (q == C)
    );

    // With EN high and SEL==11, q == D.
    check_en_high_sel_11_D: assert property (
        @(posedge clk) disable iff (1'b0) (EN && (SEL == 2'b11)) |-> (q == D)
    );

    ///// add_sub path when selected /////
    // With EN high, SEL==00, and mode==1, q == a + b.
    check_add_path_when_selected: assert property (
        @(posedge clk) disable iff (1'b0) (EN && (SEL == 2'b00) && mode) |-> (q == (a + b))
    );

    // With EN high, SEL==00, and mode==0, q == a - b.
    check_sub_path_when_selected: assert property (
        @(posedge clk) disable iff (1'b0) (EN && (SEL == 2'b00) && !mode) |-> (q == (a - b))
    );

    ///// Full combinational function equivalence /////
    // q equals the mux-of-sources with EN override and add/sub on SEL==00.
    check_full_function: assert property (
        @(posedge clk) disable iff (1'b0)
            1'b1 |-> (
                q == ( EN
                       ? ( (SEL == 2'b00) ? (mode ? (a + b) : (a - b)) :
                           (SEL == 2'b01) ? B :
                           (SEL == 2'b10) ? C : D )
                       : E )
            )
    );
endmodule