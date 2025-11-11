
module win_blk_mem_gen_prim_width__parameterized3 (
    douta10,
    douta11,
    clka,
    addra,
    dina,
    wea
);

    output [7:0] douta10;
    output douta11;
    input clka;
    input [13:0] addra;
    input [8:0] dina;
    input wea;

    // Code for the module implementation

endmodule

module block_mem
(
    input clk,
    input [12:0] addr,
    input [9:0] din,
    input we,
    output reg [9:0] dout
);

    wire [7:0] douta10;
    wire douta11;
    wire [13:0] addra;
    wire [8:0] dina;
    wire wea;

    assign addra = addr;
    assign dina = din;
    assign wea = we;

    win_blk_mem_gen_prim_width__parameterized3 mem
    (
        .douta10(douta10),
        .douta11(douta11),
        .clka(clk),
        .addra(addra),
        .dina(dina),
        .wea(wea)
    );

    always @(posedge clk) begin
        if (douta11) begin
            dout <= {1'b0, douta10};
        end
        else begin
            dout <= douta10;
        end
    end

endmodule
