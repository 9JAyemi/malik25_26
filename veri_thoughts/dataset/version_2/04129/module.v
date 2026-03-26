module io1_sub(
	       
	       sec_out, lower_out,
	       sec_io, lower_io,
	       sec_ina, lower_ina
	       );

   
   input		lower_ina;		input		sec_ina;		
   inout		lower_io;		inout		sec_io;			
   output		lower_out;		output		sec_out;		


   instio instio (
		  .lower_out		(lower_out),
		  .sec_out		(sec_out),
		  .lower_io		(lower_io),
		  .sec_io		(sec_io),
		  .lower_ina		(lower_ina),
		  .sec_ina		(sec_ina));

endmodule

module instio (
	       lower_out, sec_out,
	       lower_io, sec_io,
	       lower_ina, sec_ina
	       );

   input lower_ina;
   inout lower_io;
   output lower_out;
   input  sec_ina;
   inout  sec_io;
   output sec_out;

   wire	  lower_out = lower_ina | lower_io;
   wire	  sec_out = sec_ina | sec_io;

endmodule

