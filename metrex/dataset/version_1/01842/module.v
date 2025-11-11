
module top_module (
    input clk,
    input reset,
    input [31:0] a,
    input [31:0] b,
    input select,
    output reg [7:0] high_bit_chunk
);

    reg [31:0] sum;
    reg [2:0] high_bit_pos;
    wire [31:0] adder_out;
    wire [4:0] priority_enc_out;

    // Instantiate 32-bit adder module
    adder_32 adder_inst (
        .clk(clk),
        .reset(reset),
        .a(a),
        .b(b),
        .out(adder_out)
    );

    // Instantiate priority encoder module
    priority_encoder priority_enc_inst (
        .in(adder_out),
        .out(priority_enc_out)
    );

    // Control logic to select between adder and priority encoder
    always @ (posedge clk, posedge reset) begin
        if (reset) begin
            high_bit_pos <= 0;
            sum <= 0;
        end else begin
            if (select) begin
                high_bit_pos <= priority_enc_out;
                sum <= adder_out;
            end else begin
                high_bit_pos <= 0;
                sum <= a + b;
            end
        end
    end

    // Functional module to output high bit chunk
    always @ (high_bit_pos, sum) begin
        case (high_bit_pos)
            0: high_bit_chunk <= sum[7:0];
            1: high_bit_chunk <= sum[15:8];
            2: high_bit_chunk <= sum[23:16];
            3: high_bit_chunk <= sum[31:24];
            default: high_bit_chunk <= 8'b0;
        endcase
    end

endmodule
module adder_32 (
    input clk,
    input reset,
    input [31:0] a,
    input [31:0] b,
    output [31:0] out
);

    wire [7:0] carry;
    wire [8:0] sum1;
    wire [8:0] sum2;
    wire [8:0] sum3;
    wire [8:0] sum4;

    // Instantiate 8-bit adders
    adder_8 adder0 (
        .a(a[7:0]),
        .b(b[7:0]),
        .cin(1'b0),
        .sum(sum1)
    );
    adder_8 adder1 (
        .a(a[15:8]),
        .b(b[15:8]),
        .cin(sum1[7]),
        .sum(sum2)
    );
    adder_8 adder2 (
        .a(a[23:16]),
        .b(b[23:16]),
        .cin(sum2[7]),
        .sum(sum3)
    );
    adder_8 adder3 (
        .a(a[31:24]),
        .b(b[31:24]),
        .cin(sum3[7]),
        .sum(sum4)
    );

    // Final 8-bit adder to combine results
    assign out = sum4[7:0];

endmodule
module adder_8 (
    input [7:0] a,
    input [7:0] b,
    input cin,
    output [8:0] sum
);

    assign sum = a + b + cin;

endmodule
module priority_encoder (
    input [31:0] in,
    output reg [4:0] out
);

    always @ (in) begin
        case (in)
            32'hFFFFFFFF: out = 4'b1111;
            32'h7FFFFFFF: out = 4'b1110;
            32'h3FFFFFFF: out = 4'b1101;
            32'h1FFFFFFF: out = 4'b1100;
            32'h0FFFFFFF: out = 4'b1011;
            32'h07FFFFFF: out = 4'b1010;
            32'h03FFFFFF: out = 4'b1001;
            32'h01FFFFFF: out = 4'b1000;
            32'h00FFFFFF: out = 4'b0111;
            32'h007FFFFF: out = 4'b0110;
            32'h003FFFFF: out = 4'b0101;
            32'h001FFFFF: out = 4'b0100;
            32'h000FFFFF: out = 4'b0011;
            32'h0007FFFF: out = 4'b0010;
            32'h0003FFFF: out = 4'b0001;
            default: out = 4'b0000;
        endcase
    end

endmodule