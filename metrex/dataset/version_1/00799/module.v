module cache_memory_block (
  input clk,
  input we,
  input re,
  input [$clog2(n)-1:0] addr,
  input [m-1:0] wd,
  output [m-1:0] rd
);

parameter n = 8; // number of words
parameter m = 16; // number of bits in each word
parameter addr_bits = $clog2(n);

reg [m-1:0] cache [0:n-1]; // array to store the words

always @(posedge clk) begin
  if (we) begin
    cache[addr] <= wd;
  end
end

assign rd = (re) ? cache[addr] : 0;

endmodule