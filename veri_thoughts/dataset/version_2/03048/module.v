

module rs232in
   (input  wire        clock,

    input  wire        serial_in,
    output reg         attention = 0,
    output reg   [7:0] received_data = 0);

   parameter           bps        =     57_600;
   parameter           frequency  = 25_000_000;
   parameter           period     = (frequency + bps/2) / bps;

   reg  [16:0] ttyclk       = 0;
   wire [31:0] ttyclk_bit   = period - 2;
   wire [31:0] ttyclk_start = (3 * period) / 2 - 2;
   reg  [ 7:0] shift_in     = 0;
   reg  [ 4:0] count        = 0;

   reg         rxd          = 0;
   reg         rxd2         = 0;

   
   always @(posedge clock) begin
      attention <= 0;

      {rxd2,rxd} <= {rxd,serial_in};

      if (~ttyclk[16]) begin
         ttyclk <= ttyclk - 1'd1;
      end else if (count) begin
         if (count == 1) begin
            received_data <= {rxd2, shift_in[7:1]};
            attention     <= 1;
         end

         count       <= count - 1'd1;
         shift_in    <= {rxd2, shift_in[7:1]}; ttyclk      <= ttyclk_bit[16:0];
      end else if (~rxd2) begin
         ttyclk      <= ttyclk_start[16:0];
         count       <= 8;
      end
   end
endmodule
