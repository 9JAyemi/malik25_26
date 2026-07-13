module mux_8to1_sva (
    input logic        clk,
    input logic [3:0]  in0,
    input logic [3:0]  in1,
    input logic [3:0]  in2,
    input logic [3:0]  in3,
    input logic [3:0]  in4,
    input logic [3:0]  in5,
    input logic [3:0]  in6,
    input logic [3:0]  in7,
    input logic [2:0]  sel,
    input logic [3:0]  out
);

    // Sampled on clk; RTL has no reset and implements a combinational 8-to-1 mux.

    // sel=000 selects in0 onto out.
    check_sel_000_selects_in0: assert property (
        @(posedge clk) (sel == 3'b000) |-> (out === in0)
    );

    // sel=001 selects in1 onto out.
    check_sel_001_selects_in1: assert property (
        @(posedge clk) (sel == 3'b001) |-> (out === in1)
    );

    // sel=010 selects in2 onto out.
    check_sel_010_selects_in2: assert property (
        @(posedge clk) (sel == 3'b010) |-> (out === in2)
    );

    // sel=011 selects in3 onto out.
    check_sel_011_selects_in3: assert property (
        @(posedge clk) (sel == 3'b011) |-> (out === in3)
    );

    // sel=100 selects in4 onto out.
    check_sel_100_selects_in4: assert property (
        @(posedge clk) (sel == 3'b100) |-> (out === in4)
    );

    // sel=101 selects in5 onto out.
    check_sel_101_selects_in5: assert property (
        @(posedge clk) (sel == 3'b101) |-> (out === in5)
    );

    // sel=110 selects in6 onto out.
    check_sel_110_selects_in6: assert property (
        @(posedge clk) (sel == 3'b110) |-> (out === in6)
    );

    // sel=111 selects in7 onto out.
    check_sel_111_selects_in7: assert property (
        @(posedge clk) (sel == 3'b111) |-> (out === in7)
    );

    // out must always match the input selected by sel.
    check_out_matches_selected_input: assert property (
        @(posedge clk)
            ((sel == 3'b000) && (out === in0)) ||
            ((sel == 3'b001) && (out === in1)) ||
            ((sel == 3'b010) && (out === in2)) ||
            ((sel == 3'b011) && (out === in3)) ||
            ((sel == 3'b100) && (out === in4)) ||
            ((sel == 3'b101) && (out === in5)) ||
            ((sel == 3'b110) && (out === in6)) ||
            ((sel == 3'b111) && (out === in7))
    );

    // If sel and the selected input stay stable, out stays stable.
    check_out_stable_when_selected_path_stable: assert property (
        @(posedge clk)
            (
                (($past(sel) == 3'b000) && (sel == 3'b000) && $stable(in0)) ||
                (($past(sel) == 3'b001) && (sel == 3'b001) && $stable(in1)) ||
                (($past(sel) == 3'b010) && (sel == 3'b010) && $stable(in2)) ||
                (($past(sel) == 3'b011) && (sel == 3'b011) && $stable(in3)) ||
                (($past(sel) == 3'b100) && (sel == 3'b100) && $stable(in4)) ||
                (($past(sel) == 3'b101) && (sel == 3'b101) && $stable(in5)) ||
                (($past(sel) == 3'b110) && (sel == 3'b110) && $stable(in6)) ||
                (($past(sel) == 3'b111) && (sel == 3'b111) && $stable(in7))
            ) |-> $stable(out)
    );

endmodule