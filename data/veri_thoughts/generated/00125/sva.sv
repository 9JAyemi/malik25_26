module s5_assertions (
    input logic       clk,
    input logic [5:0] stage1_input,
    input logic [3:0] stage1_output
);

    function automatic logic [3:0] s5_expected(input logic [5:0] in);
        begin
            s5_expected = 4'd0;
            case (in)
                6'd0:  s5_expected = 4'd2;
                6'd1:  s5_expected = 4'd14;
                6'd2:  s5_expected = 4'd12;
                6'd3:  s5_expected = 4'd11;
                6'd4:  s5_expected = 4'd4;
                6'd5:  s5_expected = 4'd2;
                6'd6:  s5_expected = 4'd1;
                6'd7:  s5_expected = 4'd12;
                6'd8:  s5_expected = 4'd7;
                6'd9:  s5_expected = 4'd4;
                6'd10: s5_expected = 4'd10;
                6'd11: s5_expected = 4'd7;
                6'd12: s5_expected = 4'd11;
                6'd13: s5_expected = 4'd13;
                6'd14: s5_expected = 4'd6;
                6'd15: s5_expected = 4'd1;
                6'd16: s5_expected = 4'd8;
                6'd17: s5_expected = 4'd5;
                6'd18: s5_expected = 4'd5;
                6'd19: s5_expected = 4'd0;
                6'd20: s5_expected = 4'd3;
                6'd21: s5_expected = 4'd15;
                6'd22: s5_expected = 4'd15;
                6'd23: s5_expected = 4'd10;
                6'd24: s5_expected = 4'd13;
                6'd25: s5_expected = 4'd3;
                6'd26: s5_expected = 4'd0;
                6'd27: s5_expected = 4'd9;
                6'd28: s5_expected = 4'd14;
                6'd29: s5_expected = 4'd8;
                6'd30: s5_expected = 4'd9;
                6'd31: s5_expected = 4'd6;
                6'd32: s5_expected = 4'd4;
                6'd33: s5_expected = 4'd11;
                6'd34: s5_expected = 4'd2;
                6'd35: s5_expected = 4'd8;
                6'd36: s5_expected = 4'd1;
                6'd37: s5_expected = 4'd12;
                6'd38: s5_expected = 4'd11;
                6'd39: s5_expected = 4'd7;
                6'd40: s5_expected = 4'd10;
                6'd41: s5_expected = 4'd1;
                6'd42: s5_expected = 4'd13;
                6'd43: s5_expected = 4'd14;
                6'd44: s5_expected = 4'd7;
                6'd45: s5_expected = 4'd2;
                6'd46: s5_expected = 4'd8;
                6'd47: s5_expected = 4'd13;
                6'd48: s5_expected = 4'd15;
                6'd49: s5_expected = 4'd6;
                6'd50: s5_expected = 4'd9;
                6'd51: s5_expected = 4'd15;
                6'd52: s5_expected = 4'd12;
                6'd53: s5_expected = 4'd0;
                6'd54: s5_expected = 4'd5;
                6'd55: s5_expected = 4'd9;
                6'd56: s5_expected = 4'd6;
                6'd57: s5_expected = 4'd10;
                6'd58: s5_expected = 4'd3;
                6'd59: s5_expected = 4'd4;
                6'd60: s5_expected = 4'd0;
                6'd61: s5_expected = 4'd5;
                6'd62: s5_expected = 4'd14;
                6'd63: s5_expected = 4'd3;
            endcase
        end
    endfunction

    // Check lookup entries 0 through 7.
    check_lookup_range_0_7: assert property (
        @(posedge clk)
        (stage1_input inside {[6'd0:6'd7]}) |-> (stage1_output === s5_expected(stage1_input))
    );

    // Check lookup entries 8 through 15.
    check_lookup_range_8_15: assert property (
        @(posedge clk)
        (stage1_input inside {[6'd8:6'd15]}) |-> (stage1_output === s5_expected(stage1_input))
    );

    // Check lookup entries 16 through 23.
    check_lookup_range_16_23: assert property (
        @(posedge clk)
        (stage1_input inside {[6'd16:6'd23]}) |-> (stage1_output === s5_expected(stage1_input))
    );

    // Check lookup entries 24 through 31.
    check_lookup_range_24_31: assert property (
        @(posedge clk)
        (stage1_input inside {[6'd24:6'd31]}) |-> (stage1_output === s5_expected(stage1_input))
    );

    // Check lookup entries 32 through 39.
    check_lookup_range_32_39: assert property (
        @(posedge clk)
        (stage1_input inside {[6'd32:6'd39]}) |-> (stage1_output === s5_expected(stage1_input))
    );

    // Check lookup entries 40 through 47.
    check_lookup_range_40_47: assert property (
        @(posedge clk)
        (stage1_input inside {[6'd40:6'd47]}) |-> (stage1_output === s5_expected(stage1_input))
    );

    // Check lookup entries 48 through 55.
    check_lookup_range_48_55: assert property (
        @(posedge clk)
        (stage1_input inside {[6'd48:6'd55]}) |-> (stage1_output === s5_expected(stage1_input))
    );

    // Check lookup entries 56 through 63.
    check_lookup_range_56_63: assert property (
        @(posedge clk)
        (stage1_input inside {[6'd56:6'd63]}) |-> (stage1_output === s5_expected(stage1_input))
    );

    // If the sampled input is unchanged, the sampled output must also be unchanged.
    check_output_stable_when_input_stable: assert property (
        @(posedge clk)
        (!$initstate && $stable(stage1_input)) |-> $stable(stage1_output)
    );

    // A sampled output change must come from a sampled input change.
    check_output_change_requires_input_change: assert property (
        @(posedge clk)
        (!$initstate && $changed(stage1_output)) |-> $changed(stage1_input)
    );

endmodule