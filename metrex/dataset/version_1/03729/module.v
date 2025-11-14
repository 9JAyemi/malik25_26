
module qrs_refinement1(
    output [15:0] q_begin_ref,
    output [15:0] s_end_ref,
    output [15:0] q_begin_l3_temp,
    output [15:0] s_end_l3_temp,
    input [15:0] q_begin_l3,
    input [15:0] s_end_l3,
    input swindow1_full,
    input qwindow1_full,
    input s_end_l3_flag,
    input q_begin_l3_flag,
    input [3:0] count1,
    input [8:0] count2,
    input clk,
    input nReset
);

reg signed [15:0] q_begin_ref;
reg signed [15:0] s_end_ref;
reg signed [15:0] q_begin_l3_temp;
reg signed [15:0] s_end_l3_temp;

wire clk;
wire nReset;

always @(posedge clk or negedge nReset) begin
    if (!nReset) begin
        q_begin_ref <= 0;
        s_end_ref <= 0;
        q_begin_l3_temp <= 0;
        s_end_l3_temp <= 0;
    end else begin
        if (count1 == 2 && count2 == 1) begin
            if (qwindow1_full == 1) begin
                if (q_begin_l3_flag == 1) begin
                    q_begin_l3_temp <= q_begin_l3 - 1;
                end else begin
                    q_begin_l3_temp <= q_begin_l3_temp;
                end
            end else begin
                q_begin_l3_temp <= q_begin_l3_temp;
            end

            q_begin_ref <= q_begin_l3_temp << 3;

            if (swindow1_full == 1) begin
                if (s_end_l3_flag == 1) begin
                    s_end_l3_temp <= s_end_l3 + 2;
                end else begin
                    s_end_l3_temp <= s_end_l3_temp;
                end
            end else begin
                s_end_l3_temp <= s_end_l3_temp;
            end

            s_end_ref <= s_end_l3_temp << 3;
        end else begin
            q_begin_ref <= q_begin_ref;
            s_end_ref <= s_end_ref;
            q_begin_l3_temp <= q_begin_l3_temp;
            s_end_l3_temp <= s_end_l3_temp;
        end
    end
end

endmodule