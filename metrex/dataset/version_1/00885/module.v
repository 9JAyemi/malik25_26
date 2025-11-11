module calculator(
    input  [31:0] a,
    input  [31:0] b,
    input  reset_n,
    output  reg [31:0] add,
    output  reg [31:0] sub,
    output  reg [31:0] mul,
    output  reg [31:0] div
);

    always @(a, b, reset_n) begin
        if(!reset_n) begin
            add <= 0;
            sub <= 0;
            mul <= 0;
            div <= 0;
        end else begin
            add <= a + b;
            sub <= a - b;
            mul <= a * b;
            if(b != 0) begin
                div <= a / b;
            end else begin
                div <= 0;
            end
        end
    end

endmodule