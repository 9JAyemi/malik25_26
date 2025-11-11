module random_gen (
   input clk,      // clock signal
   input nreset,   // asynchronous reset
   input WAIT,     // enable signal
   output reg ready_random // random signal
   );

   // Generate a random signal when WAIT is asserted
   reg [8:0] ready_counter;  // Declare the counter register

   // Counter increments on every clock edge
   always @ (posedge clk or negedge nreset) begin
      if (!nreset) begin
         ready_counter <= 9'b0;   // Reset the counter on reset
      end else begin
         if (WAIT) begin
            ready_counter <= ready_counter + 1'b1;  // Increment the counter if WAIT is asserted
         end
      end
   end

   // Generate the random signal based on the counter value
   always @(*) begin
      ready_random = ready_counter[5] ^ ready_counter[4];
   end

endmodule