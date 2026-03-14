module top_module_sva (
    input logic clk,
    input logic [3:0] in,
    input logic [2:0] sel,
    input logic [1:0] out
);
    ///// Functional mapping checks /////
    // When sel=000, out == {0, in[1]}.
    check_sel000_mapping: assert property (
        @(posedge clk) disable iff (1'b0) (sel == 3'b000) |-> (out == {1'b0, in[1]})
    );
    // When sel=001, out == 2'b00.
    check_sel001_zero: assert property (
        @(posedge clk) disable iff (1'b0) (sel == 3'b001) |-> (out == 2'b00)
    );
    // When sel=010, out == {0, in[2]}.
    check_sel010_mapping: assert property (
        @(posedge clk) disable iff (1'b0) (sel == 3'b010) |-> (out == {1'b0, in[2]})
    );
    // When sel=011, out == {0, in[3]}.
    check_sel011_mapping: assert property (
        @(posedge clk) disable iff (1'b0) (sel == 3'b011) |-> (out == {1'b0, in[3]})
    );
    // When sel=100, out == 2'b00.
    check_sel100_zero: assert property (
        @(posedge clk) disable iff (1'b0) (sel == 3'b100) |-> (out == 2'b00)
    );
    // For valid selects (000..100), MSB of out is always 0.
    check_valid_sel_msb_zero: assert property (
        @(posedge clk) disable iff (1'b0)
        ((sel == 3'b000) || (sel == 3'b001) || (sel == 3'b010) || (sel == 3'b011) || (sel == 3'b100))
        |-> (out[1] == 1'b0)
    );

    ///// Stability with constant select /////
    // With sel=000 held and in[1] stable, out is stable.
    check_stable_sel000_on_in1: assert property (
        @(posedge clk) disable iff (1'b0)
        ($past(sel) == 3'b000 && sel == 3'b000 && $stable(in[1])) |-> $stable(out)
    );
    // With sel=010 held and in[2] stable, out is stable.
    check_stable_sel010_on_in2: assert property (
        @(posedge clk) disable iff (1'b0)
        ($past(sel) == 3'b010 && sel == 3'b010 && $stable(in[2])) |-> $stable(out)
    );
    // With sel=011 held and in[3] stable, out is stable.
    check_stable_sel011_on_in3: assert property (
        @(posedge clk) disable iff (1'b0)
        ($past(sel) == 3'b011 && sel == 3'b011 && $stable(in[3])) |-> $stable(out)
    );
    // With sel=001 held, out remains 2'b00.
    check_stable_sel001_zero: assert property (
        @(posedge clk) disable iff (1'b0)
        ($past(sel) == 3'b001 && sel == 3'b001) |-> (out == 2'b00)
    );
endmodule