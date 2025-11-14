
module stack(
    input reset,
    input clock,
    input nip,
    input dup,
    input we,
    input [7:0] data_in,
    output [7:0] tos_out,
    output [7:0] nos_out
);

    parameter DEPTH = 16;
    parameter PTR = $clog2(DEPTH);

    reg [7:0] cells [DEPTH-1:0];
    reg [PTR-1:0] sp;
    reg [PTR-1:0] nsp;
    reg [7:0] tos;
    reg [7:0] nos;

    always @(*) begin
        nsp = sp - 1;
    end

    assign tos_out = cells[sp];
    assign nos_out = cells[nsp];

    always @(posedge clock) begin
        if (reset) begin
            sp <= 4'b0000;
            cells[sp] <= 8'b0;
            tos <= 8'b0;
            nos <= 8'b0;
        end

        tos <= cells[sp];
        nos <= cells[nsp];

        if (nip && !dup) begin
            sp <= sp - 1;
        end

        if (dup && !nip) begin
            sp <= sp + 1;
        end

        if (dup && nip) begin
            cells[nsp] <= tos;
            tos <= nos;
        end

        if (we) begin
            tos <= data_in;
        end

        cells[sp] <= tos;
    end

endmodule