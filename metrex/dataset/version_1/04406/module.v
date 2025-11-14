module low_blk_mem_gen
    (
    output reg [11:0] douta,
    input clka,
    input [10:0] addra,
    input [11:0] dina,
    input wea
    );

    reg [11:0] memory [0:2047];

    always @(posedge clka) begin
        if (wea) begin
            memory[addra] <= dina;
        end
        douta <= memory[addra];
    end

endmodule