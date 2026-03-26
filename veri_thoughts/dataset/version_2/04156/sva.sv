module mux4to1_enable_sva (
    input logic [3:0] in,
    input logic [1:0] sel,
    input logic ena,
    input logic out
);

    // The next sampled output matches the bit selected on the previous enable edge.
    check_capture_selected_bit: assert property (
        @(posedge ena)
        1'b1 |=> (
            (($past(sel) == 2'b00) && (out == $past(in[0]))) ||
            (($past(sel) == 2'b01) && (out == $past(in[1]))) ||
            (($past(sel) == 2'b10) && (out == $past(in[2]))) ||
            (($past(sel) == 2'b11) && (out == $past(in[3])))
        )
    );

    // sel=0 captures in[0] on an enable rising edge.
    check_sel0_capture: assert property (
        @(posedge ena)
        (sel == 2'b00) |=> (out == $past(in[0]))
    );

    // sel=1 captures in[1] on an enable rising edge.
    check_sel1_capture: assert property (
        @(posedge ena)
        (sel == 2'b01) |=> (out == $past(in[1]))
    );

    // sel=2 captures in[2] on an enable rising edge.
    check_sel2_capture: assert property (
        @(posedge ena)
        (sel == 2'b10) |=> (out == $past(in[2]))
    );

    // sel=3 captures in[3] on an enable rising edge.
    check_sel3_capture: assert property (
        @(posedge ena)
        (sel == 2'b11) |=> (out == $past(in[3]))
    );

endmodule