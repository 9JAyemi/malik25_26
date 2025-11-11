
module shift_register(
    input clk,
    input areset, // async active-high reset to zero
    input load,
    input ena,
    input [3:0] data,
    output reg [3:0] q,
    output [3:0] q_next);

    reg [3:0] reg1, reg2, reg3, reg4;

    always @(posedge clk or negedge areset) begin
        if (areset == 0) begin
            reg1 <= 4'b0;
            reg2 <= 4'b0;
            reg3 <= 4'b0;
            reg4 <= 4'b0;
        end else begin
            if (ena == 1) begin
                if (load == 1) begin
                    reg1 <= data;
                    reg2 <= 4'b0;
                    reg3 <= 4'b0;
                    reg4 <= 4'b0;
                end else begin
                    reg1 <= reg2;
                    reg2 <= reg3;
                    reg3 <= reg4;
                    reg4 <= 4'b0;
                end
            end
        end
    end

    assign q_next = {reg4, reg3, reg2, reg1};

    always @(posedge clk or negedge areset) begin
        if (areset == 0) begin
            q <= 4'b0;
        end else begin
            if (ena == 1) begin
                if (load == 1) begin
                    q <= data;
                end else begin
                    q <= q_next;
                end
            end
        end
    end

endmodule
module top_module(
    input clk,
    input areset, // async active-high reset to zero
    input load,
    input ena,
    input [3:0] data,
    output [3:0] q);

    wire [3:0] q_next;

    shift_register sr(clk, areset, load, ena, data, q, q_next);

endmodule