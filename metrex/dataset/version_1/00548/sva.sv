// Bind this SVA module to your fifo_reg instance(s)
// Example: bind fifo_reg fifo_reg_sva #(.WIDTH(WIDTH), .DEPTH(DEPTH)) u_fifo_reg_sva (.*);

module fifo_reg_sva #(parameter int WIDTH=8, parameter int DEPTH=4) (
  input  wire                       clk,
  input  wire                       rst,
  input  wire                       write_en,
  input  wire [WIDTH-1:0]           write_data,
  input  wire                       read_en,
  output wire [WIDTH-1:0]           read_data,
  output wire                       full,
  output wire                       empty
);

  // Reference model (scoreboard)
  int unsigned m_count;
  int unsigned m_wr_ptr, m_rd_ptr;
  logic [WIDTH-1:0] model_mem [0:DEPTH-1];

  // Handshake qualifies
  wire write_fire = write_en && !full;
  wire read_fire  = read_en  && !empty;

  // Count valid bits in DUT storage for consistency checks
  function automatic int unsigned valid_cnt();
    int unsigned s; s = 0;
    for (int i=0;i<DEPTH;i++) s += valid_reg[i];
    return s;
  endfunction

  // Reference model update + data check on reads
  always_ff @(posedge clk) begin
    if (rst) begin
      m_count  <= 0;
      m_wr_ptr <= 0;
      m_rd_ptr <= 0;
    end else begin
      if (write_fire) begin
        model_mem[m_wr_ptr] <= write_data;
        m_wr_ptr            <= (m_wr_ptr==DEPTH-1) ? 0 : m_wr_ptr+1;
      end
      if (read_fire) begin
        assert (read_data == model_mem[m_rd_ptr])
          else $error("FIFO data mismatch: rdata=%0h exp=%0h @ptr=%0d", read_data, model_mem[m_rd_ptr], m_rd_ptr);
        m_rd_ptr <= (m_rd_ptr==DEPTH-1) ? 0 : m_rd_ptr+1;
      end
      unique case ({write_fire,read_fire})
        2'b10: m_count <= m_count + 1;
        2'b01: m_count <= m_count - 1;
        default: /* no change */ ;
      endcase
    end
  end

  // -----------------------
  // Assertions
  // -----------------------

  // Reset behavior
  assert property (@(posedge clk) rst |-> (full==0 && empty==1 && ptr_write_reg==0 && ptr_read_reg==0))
    else $error("Reset state incorrect");
  assert property (@(posedge clk) rst |-> (valid_cnt()==0))
    else $error("Valid bits not cleared on reset");

  // Flags consistent with modeled occupancy
  assert property (@(posedge clk) disable iff (rst) (m_count==0) <-> empty)
    else $error("Empty flag mismatch with occupancy");
  assert property (@(posedge clk) disable iff (rst) (m_count==DEPTH) <-> full)
    else $error("Full flag mismatch with occupancy");

  // No overflow / underflow handshakes
  assert property (@(posedge clk) disable iff (rst) !(write_en && full))
    else $error("Write attempted when full");
  assert property (@(posedge clk) disable iff (rst) !(read_en && empty))
    else $error("Read attempted when empty");

  // Flags not both asserted
  assert property (@(posedge clk) disable iff (rst) !(full && empty))
    else $error("Full and Empty both asserted");

  // Pointer range (indices must stay within depth)
  assert property (@(posedge clk) (ptr_write_reg < DEPTH) && (ptr_read_reg < DEPTH))
    else $error("Pointer out of range");

  // Write pointer advances modulo DEPTH on write_fire
  assert property (@(posedge clk) disable iff (rst)
      write_fire |=> ptr_write_reg ==
                   (($past(ptr_write_reg)==DEPTH-1) ? 0 : $past(ptr_write_reg)+1))
    else $error("Write pointer did not advance correctly");

  // Read pointer advances modulo DEPTH on read_fire
  assert property (@(posedge clk) disable iff (rst)
      read_fire |=> ptr_read_reg ==
                  (($past(ptr_read_reg)==DEPTH-1) ? 0 : $past(ptr_read_reg)+1))
    else $error("Read pointer did not advance correctly");

  // No write-side state change when full (ptr stays)
  assert property (@(posedge clk) disable iff (rst)
      (full && write_en) |=> (ptr_write_reg == $past(ptr_write_reg)))
    else $error("Write pointer changed while full");

  // No read-side state change when empty (ptr stays)
  assert property (@(posedge clk) disable iff (rst)
      (empty && read_en) |=> (ptr_read_reg == $past(ptr_read_reg)))
    else $error("Read pointer changed while empty");

  // Valid bit set on successful write at the written index
  assert property (@(posedge clk) disable iff (rst)
      write_fire |=> valid_reg[$past(ptr_write_reg)] == 1'b1)
    else $error("Valid bit not set on write");

  // Valid count tracks modeled occupancy (sanity of internal bookkeeping)
  assert property (@(posedge clk) disable iff (rst)
      valid_cnt() == m_count)
    else $error("valid_reg population does not match occupancy");

  // Data captured to storage on write (internal check)
  assert property (@(posedge clk) disable iff (rst)
      write_fire |=> data_reg[$past(ptr_write_reg)] == $past(write_data))
    else $error("Data not stored correctly on write");

  // Read output stability rule: when no read occurs, the read pointer should gate changes
  // If the design allows, at least ensure read_data reflects current addressed storage
  assert property (@(posedge clk) read_data == data_reg[ptr_read_reg])
    else $error("read_data does not reflect selected storage");

  // -----------------------
  // Coverage
  // -----------------------

  // Basic write-then-read with data match
  cover property (@(posedge clk) disable iff (rst)
      write_fire ##1 !write_fire ##1 read_fire);

  // Fill to full then drain to empty
  cover property (@(posedge clk) disable iff (rst)
      (m_count==0)
      ##1 (write_en && !full)[*DEPTH]
      ##1 (full)
      ##1 (read_en && !empty)[*DEPTH]
      ##1 (empty));

  // Simultaneous read and write in steady-state
  cover property (@(posedge clk) disable iff (rst)
      (m_count>0 && m_count<DEPTH) && write_en && read_en);

  // Wrap-around on write pointer (model)
  cover property (@(posedge clk) disable iff (rst)
      $past(m_wr_ptr)==(DEPTH-1) && write_en && !full);

  // Wrap-around on read pointer (model)
  cover property (@(posedge clk) disable iff (rst)
      $past(m_rd_ptr)==(DEPTH-1) && read_en && !empty);

endmodule