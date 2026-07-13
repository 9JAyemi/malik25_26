module db_lut_tc_sva (
    input logic       clk,
    input logic [5:0] qp_i,
    input logic       mb_type_i,
    input logic [4:0] tc_o
);

    logic [5:0] qp_w;
    assign qp_w = qp_i + {mb_type_i, 1'b0};

    function automatic [4:0] expected_tc;
        input [5:0] qpw;
        begin
            case (qpw)
                6'd18, 6'd19, 6'd20, 6'd21, 6'd22, 6'd23, 6'd24, 6'd25, 6'd26: expected_tc = 5'd1;
                6'd27, 6'd28, 6'd29, 6'd30: expected_tc = 5'd2;
                6'd31, 6'd32, 6'd33, 6'd34: expected_tc = 5'd3;
                6'd35, 6'd36, 6'd37: expected_tc = 5'd4;
                6'd38, 6'd39: expected_tc = 5'd5;
                6'd40, 6'd41: expected_tc = 5'd6;
                6'd42: expected_tc = 5'd7;
                6'd43: expected_tc = 5'd8;
                6'd44: expected_tc = 5'd9;
                6'd45: expected_tc = 5'd10;
                6'd46: expected_tc = 5'd11;
                6'd47: expected_tc = 5'd13;
                6'd48: expected_tc = 5'd14;
                6'd49: expected_tc = 5'd16;
                6'd50: expected_tc = 5'd18;
                6'd51: expected_tc = 5'd20;
                6'd52: expected_tc = 5'd22;
                6'd53: expected_tc = 5'd24;
                default: expected_tc = 5'd0;
            endcase
        end
    endfunction

    // tc_o must equal the LUT value selected by qp_i plus the mb_type offset.
    check_tc_lookup_exact: assert property (
        @(posedge clk) (tc_o == expected_tc(qp_w))
    );

    // Lookup indices below 18 or above 53 must select the default zero output.
    check_tc_default_zero_outside_table: assert property (
        @(posedge clk) (((qp_w < 6'd18) || (qp_w > 6'd53)) |-> (tc_o == 5'd0))
    );

    // Lookup indices within the programmed table must produce a nonzero output.
    check_tc_nonzero_inside_table: assert property (
        @(posedge clk) (((qp_w >= 6'd18) && (qp_w <= 6'd53)) |-> (tc_o != 5'd0))
    );

endmodule