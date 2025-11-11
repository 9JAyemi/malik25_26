module ps2 (
    input CLKOUT,
    input Rx,
    output reg Tx
);

reg [8:0] data_bits;
reg parity_bit;
reg start_bit_detected;
reg [3:0] bit_count;

parameter IDLE = 2'b00;
parameter START_BIT = 2'b01;
parameter DATA_BITS = 2'b10;
parameter PARITY_BIT = 2'b11;

reg [1:0] state;

// initialize signals
initial begin
    state = IDLE;
    Tx = 1;
    data_bits = 0;
    parity_bit = 0;
    start_bit_detected = 0;
    bit_count = 0;
end

always @(posedge CLKOUT) begin
    case (state)
        IDLE: begin
            Tx = 1;
            if (Rx == 0) begin
                state = START_BIT;
                bit_count = 0;
                start_bit_detected = 1;
            end
        end
        START_BIT: begin
            Tx = 0;
            if (bit_count == 7) begin
                state = PARITY_BIT;
                bit_count = 0;
            end
            else begin
                state = DATA_BITS;
            end
            data_bits[bit_count] = Rx;
            bit_count = bit_count + 1;
        end
        DATA_BITS: begin
            Tx = data_bits[bit_count];
            if (bit_count == 7) begin
                state = PARITY_BIT;
                bit_count = 0;
            end
            else begin
                bit_count = bit_count + 1;
            end
        end
        PARITY_BIT: begin
            if (parity_bit == 1) begin
                Tx = 0;
            end
            else begin
                Tx = 1;
            end
            state = IDLE;
            if (start_bit_detected == 1) begin
                parity_bit = ^data_bits;
                start_bit_detected = 0;
            end
        end
    endcase
end

endmodule