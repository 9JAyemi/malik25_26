
module SPI_sender(
    input CLK,
    input RST,
    input [7:0] DATA,
    input [31:0] T_DIV,
    input ST,
    output SCK,
    output MOSI,
    output reg SS,
    output reg DONE
);

reg [31:0] counter;
reg [7:0] shift_register;
reg [7:0] data_out;
reg [3:0] bit_counter;
reg ss_done;

assign MOSI = shift_register[7-bit_counter];
assign SCK = counter < (T_DIV/2);

always @(posedge CLK) begin
    if (RST) begin
        counter <= 0;
        shift_register <= 0;
        data_out <= 0;
        bit_counter <= 0;
        ss_done <= 0;
        DONE <= 0;
    end else if (ST) begin
        if (counter < T_DIV) begin
            counter <= counter + 1;
        end else begin
            counter <= 0;
            if (!ss_done) begin
                SS <= 0;
                ss_done <= 1;
            end else begin
                if (bit_counter < 7) begin
                    shift_register <= {DATA[bit_counter], shift_register[7:1]};
                    bit_counter <= bit_counter + 1;
                end else begin
                    data_out <= shift_register;
                    bit_counter <= 0;
                    if (ss_done) begin
                        SS <= 1;
                        DONE <= 1;
                    end
                end
            end
        end
    end
end

endmodule
