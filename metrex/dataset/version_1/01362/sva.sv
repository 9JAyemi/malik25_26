// Bindable SVA for select_bits
module select_bits_sva #(parameter WIDTH = 16)
(
    input  signed [WIDTH-1:0] in,
    input         [9:0]       out
);

    // Parameter legality
    initial assert (WIDTH >= 10)
        else $error("select_bits: WIDTH (%0d) must be >= 10", WIDTH);

    // Functional correctness (race-safe sampling via ##0)
    property p_select_bits_ok;
        @(in or out) disable iff ($isunknown(in))
        ##0 (
            (!in[0] && (out == in[9:0])) ||
            ( in[0] && (out == in[WIDTH-1:WIDTH-10]))
        );
    endproperty
    assert property (p_select_bits_ok)
        else $error("select_bits: out mismatch. in=%0h out=%0h", in, out);

    // Known-in implies known-out
    assert property (@(in or out) !$isunknown(in) |-> ##0 !$isunknown(out))
        else $error("select_bits: X/Z on out with known in. in=%0h out=%0h", in, out);

    // Output only changes when input changes
    assert property (@(out) ##0 $changed(in))
        else $error("select_bits: out changed without in change. in=%0h out=%0h", in, out);

    // Coverage: exercise both branches
    cover property (@(in) ##0 !in[0]);
    cover property (@(in) ##0  in[0]);

    // Coverage: observe correct outcomes on each branch
    cover property (@(in) ##0 (!in[0] && (out == in[9:0])));
    cover property (@(in) ##0 ( in[0] && (out == in[WIDTH-1:WIDTH-10])));

    // Coverage: toggle between branches
    cover property (@(in) ##0 in[0]  ##1 ##0 !in[0]);
    cover property (@(in) ##0 !in[0] ##1 ##0  in[0]);

endmodule

bind select_bits select_bits_sva #(.WIDTH(WIDTH)) u_select_bits_sva (.*);