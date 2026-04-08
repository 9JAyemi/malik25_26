module s6_sva (
    input logic clk,
    input logic [5:0] stage1_input,
    input logic [3:0] stage1_output
);

function automatic logic [3:0] expected_stage1_output(input logic [5:0] in);
    begin
        expected_stage1_output = 4'd0;
        case (in)
            6'd0:  expected_stage1_output = 4'd12;
            6'd1:  expected_stage1_output = 4'd10;
            6'd2:  expected_stage1_output = 4'd1;
            6'd3:  expected_stage1_output = 4'd15;
            6'd4:  expected_stage1_output = 4'd10;
            6'd5:  expected_stage1_output = 4'd4;
            6'd6:  expected_stage1_output = 4'd15;
            6'd7:  expected_stage1_output = 4'd2;
            6'd8:  expected_stage1_output = 4'd9;
            6'd9:  expected_stage1_output = 4'd7;
            6'd10: expected_stage1_output = 4'd2;
            6'd11: expected_stage1_output = 4'd12;
            6'd12: expected_stage1_output = 4'd6;
            6'd13: expected_stage1_output = 4'd9;
            6'd14: expected_stage1_output = 4'd8;
            6'd15: expected_stage1_output = 4'd5;
            6'd16: expected_stage1_output = 4'd0;
            6'd17: expected_stage1_output = 4'd6;
            6'd18: expected_stage1_output = 4'd13;
            6'd19: expected_stage1_output = 4'd1;
            6'd20: expected_stage1_output = 4'd3;
            6'd21: expected_stage1_output = 4'd13;
            6'd22: expected_stage1_output = 4'd4;
            6'd23: expected_stage1_output = 4'd14;
            6'd24: expected_stage1_output = 4'd14;
            6'd25: expected_stage1_output = 4'd0;
            6'd26: expected_stage1_output = 4'd7;
            6'd27: expected_stage1_output = 4'd11;
            6'd28: expected_stage1_output = 4'd5;
            6'd29: expected_stage1_output = 4'd3;
            6'd30: expected_stage1_output = 4'd11;
            6'd31: expected_stage1_output = 4'd8;
            6'd32: expected_stage1_output = 4'd9;
            6'd33: expected_stage1_output = 4'd4;
            6'd34: expected_stage1_output = 4'd14;
            6'd35: expected_stage1_output = 4'd3;
            6'd36: expected_stage1_output = 4'd15;
            6'd37: expected_stage1_output = 4'd2;
            6'd38: expected_stage1_output = 4'd5;
            6'd39: expected_stage1_output = 4'd12;
            6'd40: expected_stage1_output = 4'd2;
            6'd41: expected_stage1_output = 4'd9;
            6'd42: expected_stage1_output = 4'd8;
            6'd43: expected_stage1_output = 4'd5;
            6'd44: expected_stage1_output = 4'd12;
            6'd45: expected_stage1_output = 4'd15;
            6'd46: expected_stage1_output = 4'd3;
            6'd47: expected_stage1_output = 4'd10;
            6'd48: expected_stage1_output = 4'd7;
            6'd49: expected_stage1_output = 4'd11;
            6'd50: expected_stage1_output = 4'd0;
            6'd51: expected_stage1_output = 4'd14;
            6'd52: expected_stage1_output = 4'd4;
            6'd53: expected_stage1_output = 4'd1;
            6'd54: expected_stage1_output = 4'd10;
            6'd55: expected_stage1_output = 4'd7;
            6'd56: expected_stage1_output = 4'd1;
            6'd57: expected_stage1_output = 4'd6;
            6'd58: expected_stage1_output = 4'd13;
            6'd59: expected_stage1_output = 4'd0;
            6'd60: expected_stage1_output = 4'd11;
            6'd61: expected_stage1_output = 4'd8;
            6'd62: expected_stage1_output = 4'd6;
            6'd63: expected_stage1_output = 4'd13;
        endcase
    end
endfunction

// stage1_output must match the implemented lookup table for the current input.
check_stage1_output_matches_lookup: assert property (
    @(posedge clk) stage1_output == expected_stage1_output(stage1_input)
);

endmodule