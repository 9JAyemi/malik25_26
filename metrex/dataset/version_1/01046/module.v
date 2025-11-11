module memory (
    input [9:0] address,
    input clock,
    input [11:0] data_in,
    input write_en,
    output reg [11:0] data_out
);

    reg [11:0] mem[1023:0];

    always @(posedge clock) begin
        if (write_en) begin
            mem[address] <= data_in;
        end
        data_out <= mem[address];
    end

endmodule