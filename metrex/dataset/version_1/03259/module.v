module mem_protect #(
  parameter n = 10,
  parameter m = 2
)(
  input [n-1:0] addr,
  input [m-1:0] ctrl,
  output mem_en
);


parameter memory_size = 1024; // size of the memory block to be protected.

reg mem_en;

always @(*) begin
  if (addr < memory_size && ctrl[0] && !ctrl[1]) begin
    mem_en = 1;
  end else begin
    mem_en = 0;
  end
end

endmodule