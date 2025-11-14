// SVA for ECC_memory_block
// Bind this file to the DUT.
// Focused on correctness, gating, write timing, decode equivalence, and end-to-end behavior.

module ECC_memory_block_sva #(parameter int n=8, m=4)
(
  input  logic [n-1:0]       data_in,
  input  logic               we,
  input  logic [n-1:0]       data_out,
  input  logic               re,
  // internal signals (bound hierarchically)
  input  logic [n+m-1:0]     memory_block,
  input  logic [n-1:0]       corrected_data,
  input  logic               read_enable
);

  // Local copies of DUT algorithms for precise checks
  function automatic [n+m-1:0] enc(input [n-1:0] data);
    integer i,j,parity_pos;
    begin
      for (i=0;i<n;i++) enc[i+m]=data[i];
      for (i=0;i<m;i++) begin
        parity_pos = 2**i;
        enc[parity_pos-1]=0;
        for (j=0;j<n+m;j++) if ((j+1)&parity_pos) enc[parity_pos-1]^=enc[j];
      end
    end
  endfunction

  function automatic [n-1:0] dec(input [n+m-1:0] encoded_data);
    integer i,j,parity_pos,error_pos;
    reg [n+m-1:0] corrected_encoded_data;
    begin
      error_pos=0;
      for (i=0;i<m;i++) begin
        parity_pos=2**i;
        for (j=0;j<n+m;j++) if ((j+1)&parity_pos) if (encoded_data[j]) error_pos ^= (j+1);
      end
      corrected_encoded_data = encoded_data;
      if (error_pos) corrected_encoded_data[error_pos-1] = ~corrected_encoded_data[error_pos-1];
      for (i=0;i<n;i++) dec[i]=corrected_encoded_data[i+m];
    end
  endfunction

  default clocking cb @(posedge we or negedge we or posedge re or negedge re); endclocking
  default disable iff ($isunknown({we,re}));

  // Write happens only on falling edge of we and stores enc(data_in)
  assert property ( $fell(we) |-> ##0 (memory_block == enc(data_in)) )
    else $error("memory_block not equal to enc(data_in) on negedge we");

  assert property ( $rose(we) |-> $stable(memory_block) )
    else $error("memory_block changed on posedge we");

  // Read path combinational behavior and gating
  assert property ( !re |-> ##0 (read_enable==1'b0 && corrected_data=='0 && data_out=='0) )
    else $error("Outputs not zeroed when re==0");

  assert property ( re |-> ##0 (read_enable==1'b1 && corrected_data==dec(memory_block) && data_out==corrected_data) )
    else $error("Decode/gating incorrect when re==1");

  // read_enable mirrors re; update in same timestep on re change
  assert property ( $changed(re) |-> ##0 (read_enable==re) )
    else $error("read_enable does not mirror re");

  // Basic X-safety on outputs when inputs are known
  assert property ( !$isunknown({we,re}) |-> ##0 !$isunknown({read_enable, corrected_data, data_out}) )
    else $error("X detected on outputs with known control inputs");

  // End-to-end: read returns last written data if no intervening write
  property p_read_returns_last_write;
    logic [n-1:0] d;
    ( $fell(we), d = data_in )
      |-> ( ! $fell(we) )[*0:$] ##1 ( re && data_out == d );
  endproperty
  assert property ( p_read_returns_last_write )
    else $error("Read did not return last written data (no intervening write)");

  // Coverage
  cover property ( $fell(we) );
  cover property ( $rose(re) );
  // Write then read at some later time
  cover property ( 
    ( $fell(we), automatic logic [n-1:0] d = data_in ) ##[1:$] ( re && data_out == d )
  );
  // Single-bit error in codeword corrected on read
  cover property (
    ( $fell(we), automatic logic [n-1:0] d = data_in )
      ##[1:$] ( re && $onehot( memory_block ^ enc(d) ) && data_out == d )
  );

endmodule

// Bind to DUT
bind ECC_memory_block ECC_memory_block_sva #(.n(n), .m(m)) ECC_memory_block_sva_i
(
  .data_in(data_in),
  .we(we),
  .data_out(data_out),
  .re(re),
  .memory_block(memory_block),
  .corrected_data(corrected_data),
  .read_enable(read_enable)
);