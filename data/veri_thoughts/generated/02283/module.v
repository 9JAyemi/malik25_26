module my_module (
               // Outputs
               lower_out, sec_out,
               // Inouts
               lower_io, sec_io,
               // Inputs
               lower_ina, sec_ina
               );
   
   input  lower_ina;
   inout  lower_io;
   output lower_out;
   input  sec_ina;
   inout  sec_io;
   output sec_out;
   
   wire   lower_out_wire = lower_ina | lower_io;
   wire   sec_out_wire = sec_ina | sec_io;
   
   assign lower_out = lower_out_wire;
   assign sec_out = sec_out_wire;
   
endmodule