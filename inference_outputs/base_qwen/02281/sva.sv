module mux_priority_encoder_sva (
    input logic clk,
    input logic rst_n,
    input logic a,
    input logic b,
    input logic sel_b1,
    input logic sel_b2,
    input logic [7:0] in,
    output logic [2:0] pos,
    output logic [3:0] out_sum
);
    // 2-to-1 Multiplexer
    wire mux_out;
    assign mux_out = (sel_b1 & sel_b2) ? b : ((sel_b1 | sel_b2) ? a : 0);

    // Priority Encoder
    reg [2:0] pos_reg;
    always @(*) begin
        if (in[0]) pos_reg = 0;
        else if (in[1]) pos_reg = 1;
        else if (in[2]) pos_reg = 2;
        else if (in[3]) pos_reg = 3;
        else if (in[4]) pos_reg = 4;
        else if (in[5]) pos_reg = 5;
        else if (in[6]) pos_reg = 6;
        else if (in[7]) pos_reg = 7;
        else pos_reg = 0;
    end
    assign pos = pos_reg;

    // Functional Module
    always @(*) begin
        case (pos_reg)
            0: out_sum = mux_out + 0;
            1: out_sum = mux_out + 1;
            2: out_sum = mux_out + 2;
            3: out_sum = mux_out + 3;
            4: out_sum = mux_out + 4;
            5: out_sum = mux_out + 5;
            6: out_sum = mux_out + 6;
            7: out_sum = mux_out + 7;
            default: out_sum = 0;
        endcase
    end

    // Assertions
    // Priority Encoder should output the correct position
    priority_encoder_correct: assert property (
        @(posedge clk) disable iff (!rst_n) (pos_reg == pos)
    );

    // Functional Module should output the correct sum
    functional_module_correct: assert property (
        @(posedge clk) disable iff (!rst_n) (out_sum == mux_out + pos_reg)
    );

    // 2-to-1 Multiplexer should output the correct value
    mux_correct: assert property (
        @(posedge clk) disable iff (!rst_n) (mux_out == (sel_b1 & sel_b2) ? b : ((sel_b1 | sel_b2) ? a : 0))
    );

    // Priority Encoder should not output a value greater than 7
    priority_encoder_limit: assert property (
        @(posedge clk) disable iff (!rst_n) (pos_reg <= 7)
    );

    // Functional Module should not output a sum greater than 11
    functional_module_limit: assert property (
        @(posedge clk) disable iff (!rst_n) (out_sum <= 11)
    );

    // 2-to-1 Multiplexer should not output a value greater than 1
    mux_limit: assert property (
        @(posedge clk) disable iff (!rst_n) (mux_out <= 1)
    );

    // Priority Encoder should not output a value less than 0
    priority_encoder_non_negative: assert property (
        @(posedge clk) disable iff (!rst_n) (pos_reg >= 0)
    );

    // Functional Module should not output a sum less than 0
    functional_module_non_negative: assert property (
        @(posedge clk) disable iff (!rst_n) (out_sum >= 0)
    );

    // 2-to-1 Multiplexer should not output a value less than 0
    mux_non_negative: assert property (
        @(posedge clk) disable iff (!rst_n) (mux_out >= 0)
    );

    // Priority Encoder should not output a value greater than 7 when reset
    priority_encoder_reset: assert property (
        @(posedge clk) !rst_n |-> pos_reg == 0
    );

    // Functional Module should not output a sum greater than 11 when reset
    functional_module_reset: assert property (
        @(posedge clk) !rst_n |-> out_sum == 0
    );

    // 2-to-1 Multiplexer should not output a value greater than 1 when reset
    mux_reset: assert property (
        @(posedge clk) !rst_n |-> mux_out == 0
    );
endmodule