type compiler_options =
   {
      co_output_file_name: string;
      mutable co_output_file: out_channel option;
   }
