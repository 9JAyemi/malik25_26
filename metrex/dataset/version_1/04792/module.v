module MemoryArbiter #(
  parameter n = 4 // number of memory modules
)(
  input [n-1:0] mem_req,
  input [n-1:0] mem_ack,
  output reg [n-1:0] mem_req_out,
  output reg [n-1:0] mem_ack_out
);


reg [n-1:0] req_priority; // priority scheme

always @(*) begin
  // set priority based on predefined scheme
  req_priority = {mem_req[0] & mem_ack[0], mem_req[1] & mem_ack[1], mem_req[2] & mem_ack[2], mem_req[3] & mem_ack[3]};
  
  // select highest priority request
  case(req_priority)
    4'b1000: mem_req_out = mem_req[0];
    4'b0100: mem_req_out = mem_req[1];
    4'b0010: mem_req_out = mem_req[2];
    4'b0001: mem_req_out = mem_req[3];
    default: mem_req_out = 0;
  endcase
  
  // notify memory controller when request has been processed
  mem_ack_out = 0;
  case(mem_req_out)
    mem_req[0]: mem_ack_out = mem_ack[0];
    mem_req[1]: mem_ack_out = mem_ack[1];
    mem_req[2]: mem_ack_out = mem_ack[2];
    mem_req[3]: mem_ack_out = mem_ack[3];
    default: mem_ack_out = 0;
  endcase
end

endmodule