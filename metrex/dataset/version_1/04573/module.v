
module comparator_decoder (
    input [15:0] a,
    input [15:0] b,
    input [3:0] sel,
    input mode,
    input wire clk,
    input wire reset,
    output reg [15:0] out
);

    wire eq;
    wire gt;
    wire lt;

    comparator_16bit cmp (
        .a(a),
        .b(b),
        .eq(eq),
        .gt(gt),
        .lt(lt)
    );

    wire [15:0] decoder_out;
    assign decoder_out = {3'b000, eq, gt, lt};

    wire [15:0] reg_in;
    assign reg_in = (mode == 0) ? a : b;

    reg [15:0] reg_out;
    always @(posedge clk or posedge reset) begin
        if (reset) begin
            reg_out <= 16'b0;
        end else if (decoder_out[sel] == 1) begin
            reg_out <= reg_in;
        end
    end

    always @* begin
        if (decoder_out[sel] == 1) begin
            out <= reg_out;
        end else begin
            out <= {1'b0, eq, gt, lt}; //added the missing driver
        end
    end

endmodule
module comparator_16bit (
    input [15:0] a,
    input [15:0] b,
    output reg eq,
    output reg gt,
    output reg lt
);

    always @* begin
        eq = (a == b);
        gt = (a > b);
        lt = (a < b);
    end

endmodule