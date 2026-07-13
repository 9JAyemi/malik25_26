module priority_encoder_sva (
    input  logic        clk,   // assertion clock (RTL has no clock/reset)
    input  logic [3:0]  in,
    input  logic [1:0]  ctrl,
    input  logic [1:0]  out
);
    // Combinational spec of the RTL behavior for comparison
    function automatic logic [1:0] expected_out (input logic [3:0] in_f, input logic [1:0] ctrl_f);
        case (ctrl_f)
            2'b00: begin
                case (in_f)
                    4'b0001: expected_out = 2'b00;
                    4'b0010: expected_out = 2'b01;
                    4'b0100: expected_out = 2'b10;
                    4'b1000: expected_out = 2'b11;
                    default: expected_out = 2'b00;
                endcase
            end
            2'b01: begin
                case (in_f)
                    4'b0001: expected_out = 2'b00;
                    4'b0010: expected_out = 2'b00;
                    4'b0100: expected_out = 2'b01;
                    4'b1000: expected_out = 2'b10;
                    default: expected_out = 2'b00;
                endcase
            end
            2'b10: begin
                case (in_f)
                    4'b0001: expected_out = 2'b00;
                    4'b0010: expected_out = 2'b00;
                    4'b0100: expected_out = 2'b00;
                    4'b1000: expected_out = 2'b01;
                    default: expected_out = 2'b00;
                endcase
            end
            default: begin // ctrl == 2'b11
                expected_out = 2'b00;
            end
        endcase
    endfunction

    // Out must equal the combinational mapping defined by ctrl and in.
    check_functional_mapping: assert property (
        @(posedge clk) out == expected_out(in, ctrl)
    );

    // For ctrl==11, out is always 00 regardless of in.
    check_ctrl11_zero: assert property (
        @(posedge clk) (ctrl == 2'b11) |-> (out == 2'b00)
    );

    // For ctrl==10 and in==1000, out is 01.
    check_ctrl10_map_onehot3: assert property (
        @(posedge clk) (ctrl == 2'b10 && in == 4'b1000) |-> (out == 2'b01)
    );

    // For ctrl==10 and in!=1000, out is 00.
    check_ctrl10_others_zero: assert property (
        @(posedge clk) (ctrl == 2'b10 && in != 4'b1000) |-> (out == 2'b00)
    );

    // For ctrl==01 and in==1000, out is 10.
    check_ctrl01_map_onehot3: assert property (
        @(posedge clk) (ctrl == 2'b01 && in == 4'b1000) |-> (out == 2'b10)
    );

    // For ctrl==01 and in==0100, out is 01.
    check_ctrl01_map_onehot2: assert property (
        @(posedge clk) (ctrl == 2'b01 && in == 4'b0100) |-> (out == 2'b01)
    );

    // For ctrl==01 and in==0010, out is 00.
    check_ctrl01_deprioritize_onehot1: assert property (
        @(posedge clk) (ctrl == 2'b01 && in == 4'b0010) |-> (out == 2'b00)
    );

    // For ctrl==00 and in==0001, out is 00.
    check_ctrl00_map_onehot0: assert property (
        @(posedge clk) (ctrl == 2'b00 && in == 4'b0001) |-> (out == 2'b00)
    );

    // For ctrl==00 and in==0010, out is 01.
    check_ctrl00_map_onehot1: assert property (
        @(posedge clk) (ctrl == 2'b00 && in == 4'b0010) |-> (out == 2'b01)
    );

    // For ctrl==00 and in==0100, out is 10.
    check_ctrl00_map_onehot2: assert property (
        @(posedge clk) (ctrl == 2'b00 && in == 4'b0100) |-> (out == 2'b10)
    );

    // For ctrl==00 and in==1000, out is 11.
    check_ctrl00_map_onehot3: assert property (
        @(posedge clk) (ctrl == 2'b00 && in == 4'b1000) |-> (out == 2'b11)
    );

    // For ctrl==00 and inputs not explicitly listed, out is 00.
    check_ctrl00_default_zero: assert property (
        @(posedge clk) (ctrl == 2'b00 && !(in inside {4'b0001,4'b0010,4'b0100,4'b1000})) |-> (out == 2'b00)
    );

    // For ctrl==01 and inputs not explicitly listed, out is 00.
    check_ctrl01_default_zero: assert property (
        @(posedge clk) (ctrl == 2'b01 && !(in inside {4'b0001,4'b0010,4'b0100,4'b1000})) |-> (out == 2'b00)
    );

    // For ctrl==10 and inputs not explicitly listed, out is 00.
    check_ctrl10_default_zero: assert property (
        @(posedge clk) (ctrl == 2'b10 && !(in inside {4'b0001,4'b0010,4'b0100,4'b1000})) |-> (out == 2'b00)
    );
endmodule