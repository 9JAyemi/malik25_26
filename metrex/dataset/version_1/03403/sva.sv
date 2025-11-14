// SVA checker for mux_4to1_case
module mux_4to1_case_sva #(parameter bit REQUIRE_KNOWN_SEL = 1) (
    input logic A, B, C, D,
    input logic [1:0] sel,
    input logic Y
);
    // Functional correctness on any input/select change
    property p_mux_correct;
        @(A or B or C or D or sel)
            Y === (sel===2'b00 ? A :
                   sel===2'b01 ? B :
                   sel===2'b10 ? C :
                   sel===2'b11 ? D : 1'bx);
    endproperty
    assert property (p_mux_correct)
        else $error("MUX mismatch: sel=%b Y=%b A=%b B=%b C=%b D=%b", sel,Y,A,B,C,D);

    // Optional: forbid X/Z on sel to avoid latch behavior due to missing default
    if (REQUIRE_KNOWN_SEL) begin
        property p_sel_known;
            @(sel) !$isunknown(sel);
        endproperty
        assert property (p_sel_known)
            else $error("SEL has X/Z -> latch behavior possible in mux_4to1_case");
    end

    // If all inputs and sel are known, Y must be known
    property p_no_x_on_y_when_inputs_known;
        @(A or B or C or D or sel)
            (!$isunknown({A,B,C,D,sel})) |-> !$isunknown(Y);
    endproperty
    assert property (p_no_x_on_y_when_inputs_known)
        else $error("Y is X/Z while inputs and sel are known");

    // Coverage: hit each select value and correct mapping
    cover property (@(A or B or C or D or sel) sel===2'b00 && Y===A);
    cover property (@(A or B or C or D or sel) sel===2'b01 && Y===B);
    cover property (@(A or B or C or D or sel) sel===2'b10 && Y===C);
    cover property (@(A or B or C or D or sel) sel===2'b11 && Y===D);
    // Aggregate functional cover (any legal select with correct output)
    cover property (@(A or B or C or D or sel)
        !$isunknown(sel) && Y === (sel==2'b00 ? A :
                                   sel==2'b01 ? B :
                                   sel==2'b10 ? C : D));
endmodule

// Bind into DUT
bind mux_4to1_case mux_4to1_case_sva chk(.A(A), .B(B), .C(C), .D(D), .sel(sel), .Y(Y));