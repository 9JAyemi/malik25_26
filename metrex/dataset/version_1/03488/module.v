module bit_counter (
    input CLK,
    input RST,
    input [31:0] data_in,
    output reg [4:0] count_set_bits
);

    reg [31:0] shift_reg;
    integer i;

    always @(posedge CLK or negedge RST) begin
        if (RST == 0) begin
            shift_reg <= 0;
            count_set_bits <= 0;
        end
        else begin
            shift_reg <= data_in;
            count_set_bits <= 0;
            for (i = 0; i < 32; i = i + 1) begin
                if (shift_reg[i] == 1) begin
                    count_set_bits <= count_set_bits + 1;
                end
            end
        end
    end

endmodule