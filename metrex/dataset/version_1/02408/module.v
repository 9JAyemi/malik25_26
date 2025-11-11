module top_module (
    input Clk,
    input reset,
    input [3:0] a,
    input [3:0] b,
    output reg gt,
    output reg lt,
    output reg eq
);

    reg [7:0] johnson_out;
    wire [2:0] comp_out;

    comparator comp(.a(a), .b(b), .gt(comp_out[2]), .lt(comp_out[1]), .eq(comp_out[0]));
    johnson_counter johnson(.Clk(Clk), .Y(johnson_out));

    always @(posedge Clk) begin
        if (reset) begin
            gt <= 0;
            lt <= 0;
            eq <= 0;
            johnson_out <= 8'b00000001;
        end else begin
            case (comp_out)
                3'b000: begin // a < Y < b
                    gt <= 0;
                    lt <= 0;
                    eq <= 0;
                end
                3'b001: begin // Y = b
                    gt <= 0;
                    lt <= 0;
                    eq <= 1;
                end
                3'b010: begin // a < Y
                    gt <= 1;
                    lt <= 0;
                    eq <= 0;
                end
                3'b011: begin // Y > b
                    gt <= 1;
                    lt <= 0;
                    eq <= 1;
                end
                3'b100: begin // Y = a
                    gt <= 0;
                    lt <= 1;
                    eq <= 0;
                end
                3'b101: begin // Y < a
                    gt <= 0;
                    lt <= 1;
                    eq <= 1;
                end
                3'b110: begin // Y < a or Y > b
                    gt <= 1;
                    lt <= 1;
                    eq <= 0;
                end
                3'b111: begin // Y < a or Y > b or Y = b
                    gt <= 1;
                    lt <= 1;
                    eq <= 1;
                end
            endcase

            if (johnson_out == 8'b10000000) begin
                johnson_out <= 8'b00000001;
            end else begin
                johnson_out <= johnson_out << 1;
            end
        end
    end

endmodule

module comparator (
    input [3:0] a,
    input [3:0] b,
    output reg gt,
    output reg lt,
    output reg eq
);

    always @(*) begin
        if (a > b) begin
            gt = 1;
            lt = 0;
            eq = 0;
        end else if (a < b) begin
            gt = 0;
            lt = 1;
            eq = 0;
        end else begin
            gt = 0;
            lt = 0;
            eq = 1;
        end
    end

endmodule

module johnson_counter (
    input Clk,
    output reg [7:0] Y
);

    always @(posedge Clk) begin
        if (Y == 8'b10000000) begin
            Y <= 8'b00000001;
        end else begin
            Y <= Y << 1;
        end
    end

endmodule